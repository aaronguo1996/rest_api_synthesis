import json
import re
from urllib.parse import urlparse, unquote
from witnesses.utils import add_as_object

from schemas.schema_type import SchemaType
from analyzer.entry import TraceEntry, Parameter
from openapi import defs
from analyzer.utils import name_to_path
from witnesses.utils import add_as_object

JSON_TYPE = "application/json"
HOSTNAME_PREFIX = "https://"
HOSTNAME_PREFIX_LEN = len(HOSTNAME_PREFIX)

def match_with_path(path, request_obj, url):
    # print("matching", url, "with", path)
    path_segments = path.split('/')
    url_segments = url.split('/')
    if len(path_segments) != len(url_segments):
        return None
    path_params = []
    for p, u in zip(path_segments, url_segments):
        if len(p) >= 2 and p[0] == '{' and p[-1] == '}':
            param = p[1:-1]
            if param not in request_obj:
                path_params.append({
                    "name": param,
                    "value": u,
                })
            else:
                return None
        elif p == u:
            continue
        else:
            return None
    return path_params

class LogParser:
    def __init__(self, log_file, hostname, doc,
        path_to_defs = "#/components/schemas"):
        self.log_file = log_file
        self.hostname = hostname
        self.sanitize_hostname()
        self.path_to_defs = path_to_defs
        self.doc = doc

        # update the class variable doc_obj for typeChecker
        SchemaType.doc_obj = doc

    def parse_entries(self, skips, skip_fields):
        '''
            parse the HAR file and get all the requests
        '''
        entries = []
        with open(self.log_file, 'r') as f:
            har_file = json.loads(f.read())
            har_entries = har_file["log"]["entries"]
            # exclude all the non-json responses
            entries += self._resolve_entries(har_entries, skips, skip_fields)

        return entries

    def _resolve_params(self, skip_fields, method, endpoint, request):
        # get all the query data and body data
        parameters = []

        # match the endpoint names with those in the doc and get path params
        endpoints = self.doc.get("paths")
        path_params = None
        entry_params = []
        
        request_params = []
        request_params += request.get("queryString", [])

        post_data = request.get("postData", {})
        if "params" in post_data:
            post_params = post_data.get("params")
            request_params += post_params
        else:
            post_body = json.loads(post_data.get("text", "{}"))
            for k, v in post_body.items():
                request_params.append({
                    "name": k,
                    "value": v
                })

        # here we assume each parameter has associative param name
        request_obj = {}
        for rp in request_params:
            decoded_name = unquote(rp["name"])
            param_path = name_to_path(decoded_name)
            # print(endpoint, "decode", rp["name"], "into", param_path)
            request_obj = add_as_object(request_obj, param_path, unquote(rp["value"]))
            # print(endpoint, "get param object", request_obj)

        for path, path_def in endpoints.items():
            if method.lower() in path_def:
                path_params = match_with_path(path, request_obj, endpoint)
                if path_params is not None:
                    # print("Find path", path, "for entry", endpoint)
                    endpoint = path
                    entry_def = path_def.get(method.lower())
                    entry_params = TraceEntry.from_openapi_params(
                        endpoint, method, entry_def)
                    request_obj.update(path_params)
                    break

        for param_name, param_val in request_obj.items():
            if param_name in skip_fields:
                continue

            doc_param = None
            for doc_param in entry_params:
                if doc_param.arg_name == param_name:
                    break

            if doc_param is None:
                print("cannot find entry def for", endpoint)
                is_required = True
            else:
                is_required = doc_param.is_required

            p = Parameter(
                method, param_name, endpoint, [param_name],
                is_required, None, None, param_val)
            parameters.append(p)

        return endpoint, parameters

    def _resolve_response(self, entry, method, endpoint):
        response_text = entry["response"]["content"]["text"]
        response_params = json.loads(response_text)

        response = Parameter(
            method, "", endpoint, [],
            True, 0, None, response_params)

        return response

    def _resolve_entry(self, skip_fields, entry):
        '''
            resolve a request/response entry into an LogEntry object
        '''

        request = entry.get("request", None)

        if not request:
            raise Exception("Request not found in the log entry")

        # strip out the hostname part and get the real endpoint
        servers = SchemaType.doc_obj.get("servers")
        server = servers[0].get("url")
        server_result = urlparse(server)
        base_path = server_result.path
        url_obj = urlparse(request.get("url", ""))
        endpoint = url_obj.path
        if base_path != "/" and base_path == endpoint[:len(base_path)]:
            endpoint = endpoint[len(base_path):]

        if not endpoint:
            raise Exception("Endpoint not found in the request entry")

        host_len = len(self.hostname)
        if endpoint[:host_len] == self.hostname:
            endpoint = endpoint[host_len:]

        method = request.get("method", None)

        if not method:
            raise Exception("Method not found in the request entry")

        endpoint, parameters = self._resolve_params(
            skip_fields, method, endpoint, request)
        response = self._resolve_response(entry, method, endpoint)

        return TraceEntry(endpoint, method, parameters, response)

    def _resolve_entries(self, entries, skips, skip_fields):
        '''
            resolve all the traces
        '''
        result_entries = []
        for e in entries:
            should_skip = False
            for s in skips:
                if re.search(s, e["request"]["url"]):
                    should_skip = True

            if should_skip:
                continue

            if (e["response"]["content"]["mimeType"] == JSON_TYPE and
                self.hostname in e["request"]["url"]):
                entry = self._resolve_entry(skip_fields, e)
                result_entries.append(entry)

        return result_entries

    def sanitize_hostname(self):
        # check whether the provided hostname starts with https://
        # prepend it if not
        if self.hostname[:HOSTNAME_PREFIX_LEN] != HOSTNAME_PREFIX:
            self.hostname = HOSTNAME_PREFIX + self.hostname

        # check whether the provided hostname ends with /
        # remove it if exists
        if self.hostname[-1] == '/':
            self.hostname = self.hostname[:-1]

    def read_definitions(self, doc_file):
        with open(doc_file, 'r') as f:
            doc = f.read()
            return json.loads(doc)
import base64
import json
import re
from urllib.parse import urlparse

from schemas.schema_type import SchemaType
from analyzer.entry import TraceEntry, RequestParameter, ResponseParameter

JSON_TYPE = "application/json"
HOSTNAME_PREFIX = "https://"
HOSTNAME_PREFIX_LEN = len(HOSTNAME_PREFIX)

def match_with_path(path, url):
    # print("matching", url, "with", path)
    path_segments = path.split('/')
    url_segments = url.split('/')
    if len(path_segments) != len(url_segments):
        return None

    path_params = []
    for p, u in zip(path_segments, url_segments):
        if len(p) >= 2 and p[0] == '{' and p[-1] == '}':
            param = p[1:-1]
            path_params.append({
                "name": param,
                "value": u,
            })
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

        # get all the query data and body data
        parameters = []
        
        # match the endpoint names with those in the doc and get path params
        endpoints = self.doc.get("paths")
        path_params = None
        for path, path_def in endpoints.items():
            if method.lower() in path_def:
                path_params = match_with_path(path, endpoint)
                if path_params is not None:
                    # print("Find path", path, "for entry", endpoint)
                    endpoint = path
                    break
        
        request_params = path_params or []
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

        request_params = [x for x in request_params if x["name"] not in skip_fields]
        for rp in request_params:
            p = RequestParameter(method, rp["name"], endpoint, True, None, rp["value"])
            parameters.append(p)

        response_text = entry["response"]["content"]["text"]
        # for the github api, we have to base64 decode it first.
        if entry["response"]["content"].get("encoding") == "base64":
            response_text = base64.b64decode(response_text)
        response_params = json.loads(response_text)
        
        # print(endpoint, "returns", response_params)

        p = None
        if "ok" not in response_params:
            # print("Inferring types for", endpoint)
            # print(response_params)
            resp_type = SchemaType.infer_type_for(
                self.path_to_defs, skip_fields, response_params)
            p = ResponseParameter(
                method, "", endpoint, [], True, 0, resp_type, response_params)
        else:
            p = ResponseParameter(
                method, "", endpoint, [], True, 0, None, response_params)
        
        return TraceEntry(endpoint, method, parameters, p)

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

            if (e["response"]["content"]["mimeType"] is not None and
                JSON_TYPE in e["response"]["content"]["mimeType"] and
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
            

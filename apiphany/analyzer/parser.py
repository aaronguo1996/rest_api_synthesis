import json
import re
from urllib.parse import urlparse, unquote

from analyzer.entry import TraceEntry, Parameter
from analyzer.utils import name_to_path
from witnesses.utils import add_as_object
from analyzer import consts as har_consts
import consts

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
    def __init__(self, log_file, hostname, base_path, endpoints,
        path_to_defs = "#/components/schemas"):
        self._log_file = log_file
        self._hostname = hostname
        self._sanitize_hostname()
        self._path_to_defs = path_to_defs
        self._endpoints = endpoints
        self._base_path = base_path

    def parse_entries(self, skips, skip_fields):
        '''
            parse the HAR file and get all the requests
        '''
        entries = []
        with open(self._log_file, 'r') as f:
            har_file = json.loads(f.read())
            har_entries = har_file[har_consts.HAR_LOG][har_consts.HAR_ENTRIES]
            # exclude all the non-json responses
            entries += self._resolve_entries(har_entries, skips, skip_fields)

        return entries

    def _resolve_params(self, skip_fields, method, endpoint, request):
        # get all the query data and body data
        parameters = []

        # match the endpoint names with those in the doc and get path params
        endpoints = self._endpoints
        path_params = None
        
        request_params = []
        request_params += request.get(har_consts.HAR_QUERY, [])

        post_data = request.get(har_consts.HAR_POSTDATA, {})
        if har_consts.HAR_PARAMS in post_data:
            post_params = post_data.get(har_consts.HAR_PARAMS)
            request_params += post_params
        else:
            post_body = json.loads(post_data.get(har_consts.HAR_TEXT, "{}"))
            for k, v in post_body.items():
                request_params.append({
                    har_consts.HAR_NAME: k,
                    har_consts.HAR_VALUE: v
                })

        # here we assume each parameter has associative param name
        request_obj = {}
        for rp in request_params:
            decoded_name = unquote(rp[har_consts.HAR_NAME])
            param_path = name_to_path(decoded_name)
            # print(endpoint, "decode", rp["name"], "into", param_path)
            val = rp[har_consts.HAR_VALUE]
            if isinstance(val, str):
                val = unquote(val)
            request_obj = add_as_object(
                request_obj, param_path, val
            )
            # print(endpoint, "get param object", request_obj)

        entry_def = None
        for path, path_def in endpoints.items():
            method = method.upper()
            if method in path_def:
                path_params = match_with_path(path, request_obj, endpoint)
                if path_params is not None:
                    endpoint = path
                    entry_def = path_def.get(method)
                    request_obj.update(path_params)
                    break

        if entry_def is None:
            return None, [], entry_def

        for param_name, param_val in request_obj.items():
            if param_name in skip_fields:
                continue

            match_param = None
            for doc_param in entry_def.parameters:
                if doc_param.arg_name == param_name:
                    match_param = doc_param
                    break

            if match_param is None:
                # print("cannot find entry def for", endpoint)
                continue
            else:
                is_required = match_param.is_required

            p = Parameter(
                method, param_name, endpoint, [param_name],
                is_required, None, match_param.type, param_val)
            parameters.append(p)

        return endpoint, parameters, entry_def

    def _resolve_response(self, entry, method, endpoint, entry_def):
        response_text = entry.get(har_consts.HAR_RESPONSE) \
                            .get(har_consts.HAR_CONTENT) \
                            .get(har_consts.HAR_TEXT)
        response_body = json.loads(response_text)

        if entry_def.response.type is None:
            print(method, endpoint, "has no response type")

        response = Parameter(
            method, "", endpoint, [],
            True, 0, entry_def.response.type, response_body)

        return response

    def _resolve_entry(self, skip_fields, entry):
        '''
            resolve a request/response entry into an LogEntry object
        '''

        request = entry.get(har_consts.HAR_REQUEST, None)

        if not request:
            raise Exception("Request not found in the log entry")

        url_obj = urlparse(request.get(har_consts.HAR_URL, ""))
        endpoint = url_obj.path
        base_path = self._base_path
        if base_path != "/" and base_path == endpoint[:len(base_path)]:
            endpoint = endpoint[len(base_path):]

        if not endpoint:
            raise Exception("Endpoint not found in the request entry")

        host_len = len(self._hostname)
        if endpoint[:host_len] == self._hostname:
            endpoint = endpoint[host_len:]

        method = request.get(har_consts.HAR_METHOD, None)

        if not method:
            raise Exception("Method not found in the request entry")

        endpoint, parameters, entry_def = self._resolve_params(
            skip_fields, method, endpoint, request)
        if entry_def is None:
            return None

        response = self._resolve_response(entry, method, endpoint, entry_def)

        return TraceEntry(endpoint, method, None, parameters, response)

    def _resolve_entries(self, entries, skips, skip_fields):
        '''
            resolve all the traces
        '''
        result_entries = []
        for e in entries:
            should_skip = False
            for s in skips:
                if re.search(s, e[har_consts.HAR_REQUEST][har_consts.HAR_URL]):
                    should_skip = True
                    break

            if should_skip:
                continue

            mime_type = e.get(har_consts.HAR_RESPONSE) \
                        .get(har_consts.HAR_CONTENT) \
                        .get(har_consts.HAR_MIME)
            if (mime_type == consts.JSON_TYPE and
                self._hostname in e[har_consts.HAR_REQUEST][har_consts.HAR_URL]):
                entry = self._resolve_entry(skip_fields, e)
                if entry is not None:
                    result_entries.append(entry)

        return result_entries

    def _sanitize_hostname(self):
        # check whether the provided hostname starts with https://
        # prepend it if not
        if self._hostname[:consts.HOSTNAME_PREFIX_LEN] != consts.HOSTNAME_PREFIX:
            self._hostname = consts.HOSTNAME_PREFIX + self._hostname

        # check whether the provided hostname ends with /
        # remove it if exists
        if self._hostname[-1] == '/':
            self._hostname = self._hostname[:-1]

    def _read_definitions(self, doc_file):
        with open(doc_file, 'r') as f:
            doc = f.read()
            return json.loads(doc)
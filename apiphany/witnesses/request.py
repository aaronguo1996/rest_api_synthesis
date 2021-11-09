# from urllib.parse import urlencode
# from urllib.request import urlopen, Request
import requests
import logging
import json

from openapi import defs

class Connection:
    def __init__(self, hostname, base_path):
        self._hostname = hostname[:-1] if hostname[-1] == '/' else hostname
        self._base_path = base_path[:-1] if base_path[-1] == '/' else base_path
        # self._logger = logging.getLogger(__name__)

    def replace_path_params(self, endpoint, data):
        url = "https://" + self._hostname + self._base_path + endpoint

        # check for path params
        body = {}
        for param_name, param_value in data.items():
            key = f"{{{param_name}}}"
            if key in url:
                url = url.replace(key, param_value)
            else:
                body[param_name] = param_value

        return url, body

    def send_and_recv(self, endpoint, method, content_type, headers, data):
        url, body = self.replace_path_params(endpoint, data)
        headers.update({"User-Agent": "APIphany/0.1"})

        if content_type is None or content_type == defs.HEADER_FORM:
            resp = requests.request(method, url, params=body, headers=headers)
        elif content_type == defs.HEADER_JSON:
            resp = requests.request(method, url, json=body, headers=headers)
        else:
            raise Exception("unhandled content type", content_type)

        print(f"Sending to {url}/{method} the message {body}")
        return_code = resp.status_code
        resp_body = resp.text
        print(f"Getting back from {url, body} the response {resp_body}")
        return return_code, resp_body
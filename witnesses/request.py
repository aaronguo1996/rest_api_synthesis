# from urllib.parse import urlencode
# from urllib.request import urlopen, Request
import requests
import logging
import json

from openapi import defs

class Connection:
    def __init__(self, hostname, base_path):
        self._hostname = hostname
        self._base_path = base_path
        self._logger = logging.getLogger(__name__)

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

    def send_and_recv(self, endpoint, method, headers, data):
        url, body = self.replace_path_params(endpoint, data)
        headers.update({"User-Agent": "RestSyn/0.1"})
        # if isinstance(body, dict):
        #     resp = requests.request(method, url, json=body, headers=headers)
        # else:
        resp = requests.request(method, url, params=body, headers=headers)

        self._logger.info(f"Sending to {url} the message {body}")
        return_code = resp.status_code
        resp_body = resp.text
        self._logger.info(f"Getting back from {url, body} the response {resp_body}")
        return return_code, resp_body
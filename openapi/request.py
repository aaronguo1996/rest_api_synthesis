from urllib.parse import urlencode
from urllib.request import urlopen, Request
import logging
import time

from openapi import defs

class Connection:
    def __init__(self, hostname, base_path):
        self._hostname = hostname
        self._base_path = base_path
        self._logger = logging.getLogger(__name__)

    def send_and_recv(self, endpoint, headers, data):
        url = "https://" + self._hostname + self._base_path + endpoint
        params = urlencode(data).encode()
        headers.update({"User-Agent": "RestSyn/0.1"})
        req = Request(url, data=params, headers=headers)
        self._logger.info(f"Sending to {url} the message {params}")
        try:
            resp = urlopen(req)
            return_code = resp.getcode()
            resp_body = resp.read().decode(defs.UTF8)
            self._logger.info(f"Getting back from {url, params} the response {resp_body}")
            return return_code, resp_body
        except Exception as e:
            time.sleep(60)
            return 404, str(e)


    # def send_urlencoded(self, method, endpoint, headers, data):
        
    #     default_headers = {
    #         defs.HEADER_CONTENT: defs.HEADER_FORM,
    #         defs.HEADER_ACCEPT: defs.HEADER_JSON
    #     }
    #     default_headers.update(headers)
    #     url_with_params = endpoint + "?" + params if params else endpoint
    #     self._conn.request(method, url_with_params, headers=default_headers)
    #     self._logger.info(f"Sending to {endpoint} the message {params}"
    #         f" with headers {default_headers}")

    # def send_body(self, method, endpoint, headers, body):
    #     default_headers = {
    #         defs.HEADER_CONTENT: defs.HEADER_JSON,
    #         defs.HEADER_ACCEPT: defs.HEADER_JSON
    #     }
    #     default_headers.update(headers)
    #     self._conn.request(
    #         method, endpoint, json.dumps(body).encode(), default_headers)
    #     self._logger.info(f"Sending to {endpoint} the message {body}"
    #         f" with headers {default_headers}")

    # def recv(self):
    #     response = self._conn.getresponse()
    #     if response.code in defs.SUCCESS_CODES:
    #         buf = response.read()
    #         resp_str = buf.decode(defs.UTF8)
    #         self._logger.info(f"Receiving {response.code} :{resp_str}")
    #         return response.code, resp_str
    #     else:
    #         return response.code, response.reason
    #         # raise ConnectionError(response.code, response.reason)

    # def close(self):
    #     self._conn.close()
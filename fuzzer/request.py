import http.client
import urllib.parse
import json

from fuzzer.error import ConnectionError
from openapi import defs

class Connection:
    """Maintain a network connection to the host server
    """
    def __init__(self, hostname):
        """[summary]

        Args:
            hostname ([type]): [description]
        """
        self._conn = http.client.HTTPSConnection(hostname)

    def send_urlencoded(self, method, endpoint, headers, data):
        """[summary]

        Args:
            method ([type]): [description]
            endpoint ([type]): [description]
            header ([type]): [description]
            data ([type]): [description]
        """
        params = urllib.parse.urlencode(data).encode()
        default_headers = {
            defs.HEADER_CONTENT: defs.HEADER_FORM,
            defs.HEADER_ACCEPT: defs.HEADER_JSON
        }
        default_headers.update(headers)
        self._conn.request(method, endpoint, params, default_headers)

    def send_body(self, method, endpoint, headers, body):
        default_headers = {
            defs.HEADER_CONTENT: defs.HEADER_JSON,
            defs.HEADER_ACCEPT: defs.HEADER_JSON
        }
        default_headers.update(headers)
        self._conn.request(method, endpoint, json.dumps(body).encode(), default_headers)

    def recv(self):
        """[summary]

        Raises:
            ConnectionError: [description]

        Returns:
            [type]: [description]
        """
        response = self._conn.getresponse()
        if response.code in defs.SUCCESS_CODES:
            buf = response.read()
            resp_str = buf.decode(defs.UTF8)
            return response.code, resp_str
        else:
            return response.code, response.reason
            # raise ConnectionError(response.code, response.reason)

    def close(self):
        self._conn.close()
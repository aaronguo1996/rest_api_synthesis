import json
import os
import argparse
from urllib.parse import urlparse, parse_qs

from traces import log

JSON_TYPE = "application/json"
HOSTNAME_PREFIX = "https://"
HOSTNAME_PREFIX_LEN = len(HOSTNAME_PREFIX)

class LogParser:
    def __init__(self, log_file, hostname):
        self.log_file = log_file
        self.hostname = hostname
        self.sanitize_hostname()

    def parse_entries(self):
        '''
            parse the HAR file and get all the requests
        '''
        entries = []
        with open(self.log_file, 'r') as f:
            har_file = json.loads(f.read())
            har_entries = har_file["log"]["entries"]
            # exclude all the non-json responses
            entries += self.resolve_entries(har_entries)

        return entries

    def resolve_entry(self, entry):
        '''
            resolve a request/response entry into an LogEntry object
        '''

        request = entry.get("request", None)

        if not request:
            raise Exception("Request not found in the log entry")

        # strip out the hostname part and get the real endpoint
        url_obj = urlparse(request.get("url", ""))
        endpoint = url_obj.path

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

        request_params = request.get("queryString", [])
        
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

        for rp in request_params:
            p = log.RequestParameter(rp["name"], endpoint, rp["value"])
            parameters.append(p)

        responses = []
        response_text = entry["response"]["content"]["text"]
        response_params = json.loads(response_text)
        for k, v in response_params.items():
            # flatten the returned object
            p = log.ResponseParameter(k, endpoint, [k], v)
            responses += p.flatten()

        return log.LogEntry(endpoint, method, parameters, responses)

    def resolve_entries(self, entries):
        '''
            resolve all the traces
        '''
        # print(self.entries[-1])
        result_entries = []

        for e in entries:
            if (e["response"]["content"]["mimeType"] == JSON_TYPE and
                self.hostname in e["request"]["url"]):
                entry = self.resolve_entry(e)
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

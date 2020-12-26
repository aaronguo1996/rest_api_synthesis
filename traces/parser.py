import json
import os
import argparse
from haralyzer import HarParser, HarPage

from traces import log

JSON_TYPE = "application/json"
HOSTNAME_PREFIX = "https://"
HOSTNAME_PREFIX_LEN = len(HOSTNAME_PREFIX)

class LogParser:
    def __init__(self, log_file, hostname):
        self.log_file = log_file
        self.hostname = hostname
        self.entries = []
        self.sanitize_hostname()

    def parse_entries(self):
        '''
        parse the HAR file and get all the requests
        '''
        with open(self.log_file, 'r') as f:
            har_parser = HarParser(json.loads(f.read()))
            for page in har_parser.pages:
                assert isinstance(page, HarPage)
                # exclude all the non-json responses
                entries = self.resolve_entries(page.entries)
                self.entries += entries

    def resolve_entry(self, entry):
        '''
        resolve a request/response entry into an LogEntry object
        '''

        # strip out the hostname part and get the real endpoint
        endpoint = entry["request"]["url"]
        host_len = len(self.hostname)
        if endpoint[:host_len] == self.hostname:
            endpoint = endpoint[host_len:]

        method = entry["request"]["method"]

        # get all the query data and body data
        parameters = []
        request_params = entry["request"]["queryString"]

        post_data = entry["request"]["postData"]
        if post_data["params"]:
            request_params += post_data["params"]
        else:
            post_body = json.loads(post_data["text"])
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
            p = log.ResponseParameter(k, [], v)
            responses = p.flatten()

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

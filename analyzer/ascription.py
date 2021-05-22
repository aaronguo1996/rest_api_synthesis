from analyzer.utils import make_response_name
from analyzer.entry import TraceEntry, Parameter
from schemas import types

class Ascription:
    def __init__(self, analyzer, skip_fields):
        self._analyzer = analyzer
        self._skip_fields = skip_fields

    def ascribe_response(self, endpoint, method, response):
        results = []
        responses = response.flatten_ad_hoc(self._skip_fields)
        responses = [self._analyzer.set_type(resp) for resp in responses]
        # add projections for ad-hoc objects
        if len(responses) > 1:
            resp_name = make_response_name(endpoint, method)
            resp_type = (resp_name, None)
            resp_param = Parameter(
                method, "", endpoint, [], 
                True, None, resp_type, None)
            entry_response = Parameter(
                method, "", endpoint, [], 
                True, 0, resp_type, None)
        
            for resp_return in responses:
                e = TraceEntry(
                    f"{resp_name}, {'.'.join(resp_return.path)})",
                    "", [resp_param], resp_return
                )
                results.append(e)
        else:
            entry_response = responses[0]

        return entry_response, results

    def ascribe_type(self, endpoint, method, entry_def):
        entry = TraceEntry.from_openapi(
            endpoint, method, entry_def,
        )

        parameters = []
        for p in entry.parameters:
            # decompose ad-hoc objects if necessary
            params = p.flatten_ad_hoc(self._skip_fields)
            parameters += [self._analyzer.set_type(param) for param in params]
        entry.parameters = parameters

        entry.response, results = self.ascribe_response(
            endpoint, method, 
            entry.response
        )
        results.append(entry)
        
        return results
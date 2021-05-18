from analyzer.entry import TraceEntry, Parameter
from schemas.schema_type import SchemaType

class Ascription:
    def __init__(self, analyzer):
        self._analyzer = analyzer

    def ascribe_type(self, endpoint, method, entry_def):
        results = []

        entry = TraceEntry.from_openapi(
            endpoint, method, entry_def,
        )

        params = []
        for p in entry.parameters:
            # decompose ad-hoc objects if necessary
            params += self._analyzer.set_type(p)
        entry.parameters = params

        responses = self._analyzer.set_type(entry.response)
        # add projections for ad-hoc objects
        if len(responses) > 1:
            resp_type = SchemaType(
                f"{endpoint}_{method.upper()}_response", None)
            resp_param = Parameter(
                method, "", endpoint, [], 
                True, None, resp_type, None)
            entry.response = Parameter(
                method, "", endpoint, [], 
                True, 0, resp_type, None)
        
            for resp_return in responses:
                if endpoint == "/v1/prices":
                    print(resp_return.path)
                    
                e = TraceEntry(
                    f"projection({endpoint}_{method.upper()}_response, "
                    f"{'.'.join(resp_return.path)})",
                    "", [resp_param], resp_return
                )
                results.append(e)
        else:
            entry.response = responses[0]
            
        results.append(entry)
        
        return results
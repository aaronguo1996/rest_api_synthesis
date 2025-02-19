from analyzer.entry import TraceEntry

class Ascription:
    def __init__(self, analyzer, skip_fields):
        self._analyzer = analyzer
        self._skip_fields = skip_fields

    def ascribe_type(self, entry, infer_type=True):
        parameters = []
        for p in entry.parameters:
            # decompose ad-hoc objects if necessary
            params = p.flatten_ad_hoc(self._skip_fields)
            parameters += [self._analyzer.set_type(param, infer_type) for param in params]
        
        results = entry.response.project_ad_hoc(self._analyzer, infer_type)
        response = self._analyzer.set_type(entry.response, infer_type)

        results.append(TraceEntry(
            entry.endpoint,
            entry.method,
            entry.content_type,
            parameters,
            response,
        ))
        
        return results

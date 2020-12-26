class LogAnalyzer:
    def __init__(self, entries):
        self.entries = entries

    def analyze(self):
        raise NotImplementedError

    def match(self):
        '''
        Compare each pair of traces and find the common values between them
        '''
        raise NotImplementedError
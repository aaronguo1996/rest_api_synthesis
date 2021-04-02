from synthesizer.synthesizer import Synthesizer

def init_synthesizer(doc, configuration, analyzer):
    global synthesizer
    synthesizer = Synthesizer(doc, configuration, analyzer)
    synthesizer.init()
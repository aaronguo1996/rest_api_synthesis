from synthesizer.synthesizer import Synthesizer

def init_synthesizer(doc, configuration, analyzer, exp_dir):
    global synthesizer
    synthesizer = Synthesizer(doc, configuration, analyzer, exp_dir)
    synthesizer.init()
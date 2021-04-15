from collections import defaultdict

from synthesizer.synthesizer import Synthesizer

def init_synthesizer(doc, configuration, analyzer, exp_dir):
    global synthesizer
    synthesizer = Synthesizer(doc, configuration, analyzer, exp_dir)
    synthesizer.init()

def get_petri_net_data():
    num_place = len(synthesizer._encoder._net.place())
    num_trans = len(synthesizer._encoder._net.transition())
    return num_place, num_trans

def get_solution_strs(solutions):
    counter = defaultdict(int)
    [r.pretty(synthesizer._entries, counter) for r in solutions]
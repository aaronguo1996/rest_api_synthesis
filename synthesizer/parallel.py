from collections import defaultdict
import time
from functools import partial
import multiprocessing as mp
import concurrent.futures as cf

from synthesizer.petrinet_encoder import PetriNetEncoder
from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.utils import DEFAULT_LENGTH_LIMIT
import globs

def run_encoder(inputs, outputs, path_len):
    input_map = defaultdict(int)
    for _, typ in inputs.items():
        input_map[typ.name] += 1

    output_map = defaultdict(int)
    for typ in outputs:
        output_map[typ.name] += 1
        
    solver_type = globs.synthesizer._config["synthesis"]["solver_type"]
    if solver_type == "petri net":
        encoder = PetriNetEncoder({})
    elif solver_type == "hypergraph":
        encoder = HyperGraphEncoder({})
    else:
        raise Exception("Unknown solver type in config")

    for e in globs.synthesizer._unique_entries.values():
        encoder._add_transition(e)

    solutions = set()
    start = time.time()
    path = encoder.get_length_of(path_len, input_map, output_map)
    while path is not None:
        end = time.time()
        programs, perms = globs.synthesizer._generate_solutions(
            path_len, inputs, outputs, path, end - start
        )
        solutions = solutions.union(set(programs))
        if programs:
            encoder.block_prev(perms)
            path = encoder.solve()

    print("Finished encoder running for path length", path_len, 
        "after time", time.time() - start, flush=True)
    return solutions

def spawn_encoders(inputs, outputs, solver_num):
    # with mp.Pool(solver_num) as pool:
    #     # pool.map(
    #     #     partial(run_encoder, inputs, outputs),
    #     #     range(DEFAULT_LENGTH_LIMIT),
    #     # )
    #     results = []
    #     for i in range(DEFAULT_LENGTH_LIMIT):
    #         result = pool.apply_async(run_encoder, args=(inputs, outputs, i))
    #         results.append(result)

    #     for result in results:
    #         result.get()

    with cf.ProcessPoolExecutor(max_workers=solver_num) as executor:
        futures = executor.map(
            partial(run_encoder, inputs, outputs),
            range(DEFAULT_LENGTH_LIMIT),
        )
        for future in cf.as_completed(futures):
            print(future.result)
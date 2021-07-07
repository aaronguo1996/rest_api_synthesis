from collections import defaultdict
import concurrent.futures as cf
import multiprocessing
import os
import pebble
import time

from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.ilp_encoder import ILPetriEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
import consts

def run_encoder(synthesizer, inputs, outputs, path_len, solutions):
    input_map = defaultdict(int)
    for _, typ in inputs.items():
        typ_name = str(typ.ignore_array())
        input_map[typ_name] += 1

    output_map = defaultdict(int)
    for typ in outputs:
        typ_name = str(typ.ignore_array())
        output_map[typ_name] += 1
        
    config = synthesizer._config
    solver_type = config[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_TYPE]
    if solver_type == consts.SOLVER_PN_SMT:
        encoder = PetriNetEncoder({})
    elif solver_type == consts.SOLVER_PN_ILP:
        encoder = ILPetriEncoder({})
    elif solver_type == consts.SOLVER_HYPER:
        encoder = HyperGraphEncoder({})
    else:
        raise Exception("Unknown solver type in config")

    for name, e in synthesizer._unique_entries.items():
        encoder.add_transition(name, e)

    # write encoder stats to file
    if path_len == 1:
        encoder_path = os.path.join(synthesizer._exp_dir, "encoder.txt")
        with open(encoder_path, "w") as f:
            f.write(str(len(encoder._net.place())))
            f.write("\n")
            f.write(str(len(encoder._net.transition())))

    solution_set = set()
    start = time.time()
    path = encoder.get_length_of(path_len, input_map, output_map)
    while path is not None:
        # print("Finding a path", path,"in", time.time() - start, "seconds at path length", path_len, flush=True)

        end = time.time()
        # print(path)
        programs, perms = synthesizer._generate_solutions(
            path_len, inputs, outputs, path, end - start
        )

        for p in set(programs):
            if p not in solution_set:
                solution_set.add(p)
                solutions.put(p)

        # solution_set = solution_set.union(set(programs))
        
        encoder.block_prev(perms)
        path = encoder.solve()

    print("Finished encoder running for path length", path_len, 
        "after time", time.time() - start, flush=True)

def spawn_encoders(synthesizer, inputs, outputs, solver_num, timeout=60):
    m = multiprocessing.Manager()
    all_solutions = []
    for i in range(consts.DEFAULT_LENGTH_LIMIT + 1):
        solutions = m.Queue()
        all_solutions.append(solutions)

    with pebble.ProcessPool() as pool:
        futures = []
        for i in range(consts.DEFAULT_LENGTH_LIMIT + 1):
            future = pool.schedule(
                run_encoder, 
                args=(synthesizer, inputs, outputs, i, all_solutions[i]),
                timeout=timeout,
                )
            futures.append(future)
        
    for i, future in enumerate(futures):
        try:
            future.result(timeout=timeout)
            # print(f"Completed for path length {i}")
        except cf.TimeoutError:
            pass
            # print(f"Killed path length {i} due to timeout")

    for i, progs in enumerate(all_solutions):
        # print(i, progs.qsize(), flush=True)
        prog_list = []
        while not progs.empty():
            item = progs.get_nowait()
            if item is None:
                break

            prog_list.append(item)
            
        # progs.task_done()

        synthesizer._serialize_solutions(i, prog_list)

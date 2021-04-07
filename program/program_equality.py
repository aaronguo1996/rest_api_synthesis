import re

def replace_variables(progstr):
    vnames = re.findall("x\d+", progstr)
    varnames = []
    dups = set()
    for vname in vnames:
        if not vname in dups:
            dups.add(vname)
            varnames.append(vname)

    for i, vname in enumerate(varnames):
        progstr = str.replace(progstr, vname, f"x{i}")

    return progstr

def compare_program_strings(progstr_a, progstr_b):
    return replace_variables(progstr_a) == replace_variables(progstr_b)

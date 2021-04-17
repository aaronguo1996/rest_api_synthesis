import re

def replace_variables(progstr):
    vnames = re.findall("x\d+", progstr)
    varnames = []
    for vname in vnames:
        if not vname in varnames:
            varnames.append(vname)

    for i, vname in enumerate(varnames):
        progstr = str.replace(progstr, vname, f"x{i}")

    # Remove all whitespace here
    # TODO: is this good?
    progstr = re.sub("\s", "", progstr)
    progstr = re.sub("\n", "", progstr)
    return progstr

def compare_program_strings(progstr_a, progstr_b):
    # Since we remove all whitespace in replace_variables, this isn't necessarily needed,
    # but whatever lmao
    return [x.strip() for x in replace_variables(progstr_a).split('\n')] == [x.strip() for x in replace_variables(progstr_b).split('\n')]

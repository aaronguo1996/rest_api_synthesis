def split_by(p, lst):
    good = [x for x in lst if p(x)]
    bad = [x for x in lst if not p(x)]
    return good, bad
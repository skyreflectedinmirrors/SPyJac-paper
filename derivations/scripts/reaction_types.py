from enum import IntEnum

class reaction_type(IntEnum):
    elementary = 1
    thd = 2
    pdep = 3
    plog = 4
    cheb = 5

class thd_body_type(IntEnum):
    mix = 1
    single = 2
    unity = 3

class pdep_form(IntEnum):
    none = 1
    fall = 2
    chem = 3

class falloff_form(IntEnum):
    lind = 1
    troe = 2
    sri = 3

class reversible_type(IntEnum):
    none = 1
    explicit = 2
    non_explicit = 3
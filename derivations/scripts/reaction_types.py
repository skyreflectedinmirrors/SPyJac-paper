from enum import IntEnum

class reaction_type(IntEnum):
    elementary = 1
    thd = 2
    fall = 3
    chem = 4
    plog = 5
    cheb = 6

class thd_body_type(IntEnum):
    mix = 1
    species = 2
    unity = 3

class falloff_form(IntEnum):
    lind = 1
    troe = 2
    sri = 3

class reversible_type(IntEnum):
    none = 1
    explicit = 2
    non_explicit = 3
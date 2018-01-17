from __future__ import print_function
from sympy import symbols, log, exp, limit, KroneckerDelta, diff, \
    Product, factor, Pow, Symbol, simplify, Limit
from optionloop import OptionLoop


def __get_dci(fall_type='chem', blend_type='troe', pr_type='mix', var='E'):
    # create temperature
    T = symbols('T')

    # create kf's
    kf, kinf = symbols('kf kinf', real=True, nonnegative=True)

    # create third body efficiency & volume
    V, C, P = symbols('V C P', real=True, nonnegative=True)
    Xi, alphaNS, alphaj = symbols('Xi alphaNS alphaj', real=True)

    # species
    m, Ns, j = symbols('m Ns j', integer=True, nonnegative=True)

    # create pr
    Pr = kf * Xi / kinf
    R = 8.314

    # create Fi & Troe params
    if blend_type == 'troe':
        T1, T2, T3, a = symbols('T1 T2 T3 a', real=True)

        Fcent = a * exp(-T / T1) + (1 - a) * exp(-T / T3) + exp(-T2 / T)
        Atroe = -0.68 * log(Fcent, 10) + log(Pr, 10) - 0.4
        Btroe = -1.1762 * log(Fcent, 10) - 0.14 * log(Pr, 10) + 0.806

        Fi = Fcent ** (1 / (1 + (Atroe / Btroe)**2))
    elif blend_type == 'sri':
        a, b, c, d, e = symbols('a b c d e', real=True)
        X = 1 / (log(Pr, 10) ** 2 + 1)
        Fi = d * T**e * (a * exp(-b / T) + exp(-T / c)) ** X
    elif blend_type == 'lind':
        Fi = 1

    # chemically activated form
    if fall_type == 'chem':
        ci = Fi / (1 + Pr)
    elif fall_type == 'fall':
        ci = Pr * Fi / (1 + Pr)

    # now create derivative temporary products (assuming mixture)
    if var == 'T':
        b0, binf, e0, einf = symbols('b0 binf e0 einf', real=True)
        if pr_type in ['mix', 'spec']:
            Theta_Pr = (b0 - binf + e0 / (R * T) - einf / (R * T)) / T
            if pr_type == 'mix':
                theta_Pr = -C * kf * alphaNS / (T * kinf)
            else:
                theta_Pr = -C * kf * KroneckerDelta(m, Ns) / (T * kinf)
        elif pr_type == 'unity':
            Theta_Pr = (b0 - binf + e0 / (R * T) - einf / (R * T)) / T
            theta_Pr = 0
    elif var == 'nj':
        Theta_Pr = 0
        if pr_type == 'mix':
            theta_Pr = alphaj - alphaNS
        elif pr_type == 'unity':
            theta_Pr = 0
        elif pr_type == 'spec':
            theta_Pr = KroneckerDelta(m, j) - KroneckerDelta(m, Ns)
    elif var == 'V':
        # conp derivative w.r.t. volume
        if pr_type == 'mix':
            Theta_Pr = -1 / V
            theta_Pr = C * kf * alphaNS / (kinf * T)
        elif pr_type == 'unity':
            Theta_Pr = 0
            theta_Pr = 0
        elif pr_type == 'spec':
            m, Ns = symbols('m Ns', integer=True, nonnegative=True)
            Theta_Pr = -1 / V
            theta_Pr = C * kf * KroneckerDelta(m, Ns) / (kinf * T)
    elif var == 'P':
        Theta_Pr = 0
        # conv derivative w.r.t. pressure
        if pr_type == 'mix':
            theta_Pr = kf * alphaNS / (kinf * R * T)
        elif pr_type == 'unity':
            theta_Pr = 0
        elif pr_type == 'spec':
            theta_Pr = kf * KroneckerDelta(m, Ns) / (kinf * R * T)

    # now create blending function products
    if blend_type == 'lind':
        Theta_Fi = 0
    elif blend_type == 'troe':
        if var == 'T':
            Theta_Fi = - Btroe / (Fcent * Pr * (Atroe**2 + Btroe**2)**2 * log(10)) * (
                2 * Atroe * Fcent * (0.14 * Atroe + Btroe) * (
                    Pr * Theta_Pr + theta_Pr) * log(Fcent) + Pr * diff(Fcent, T) * (
                        2 * Atroe * (1.1762 * Atroe - 0.67 * Btroe) * log(Fcent) -
                        Btroe * (Atroe**2 + Btroe**2) * log(10))
            )
        elif var == 'nj':
            Theta_Fi = -2 * Atroe * Btroe * (0.14 * Atroe + Btroe) * log(Fcent) / (
                Pr * (Atroe**2 + Btroe**2)**2 * log(10))
        elif var == 'V':
            Theta_Fi = (-2 * Atroe * Btroe * log(Fcent) /
                        (Pr * (Atroe**2 + Btroe**2)**2 * log(10))) * \
                       (0.14 * Atroe + Btroe) * (Pr * Theta_Pr + theta_Pr)
        elif var == 'P':
            Theta_Fi = -2 * Atroe * Btroe * theta_Pr * (0.14 * Atroe + Btroe) * log(Fcent) / (
                Pr * (Atroe**2 + Btroe**2)**2 * log(10))
    elif blend_type == 'sri':
        if var == 'T':
            Theta_Fi = -X * (exp(-T / c) / c - a * b * exp(-b / T) / (T**2)) / (
                a * exp(-b / T) + exp(-T / c)) + e / T - ((
                    2 * X**2 * log(a * exp(-b / T) + exp(-T / c))) / (Pr * log(10)**2) * (
                    (Theta_Pr * Pr + theta_Pr) * log(Pr))
            )
        elif var == 'nj':
            Theta_Fi = -2 * X**2 * \
                log(a * exp(-b / T) + exp(-T / c)) * \
                log(Pr) / (Pr * log(10)**2)
        elif var == 'V':
            Theta_Fi = (-2 * X**2 * log(Pr) / (Pr * log(10)**2)) * (Theta_Pr * Pr + theta_Pr) * log(
                (a * exp(T / c) + exp(b / T)) * exp(-T / c - b / T))
        elif var == 'P':
            Theta_Pr = (-2 * X**2 * theta_Pr * log(Pr) /
                        (Pr * log(10)**2)) * log(a * exp(-b / T) + exp(-T / c))

    # and finally give dci
    if var == 'T':
        if fall_type == 'fall':
            dci = Fi * theta_Pr / (Pr + 1) + (-Pr * Theta_Pr / (Pr + 1) + Theta_Fi +
                                              Theta_Pr - theta_Pr / (Pr + 1)) * ci
        elif fall_type == 'chem':
            dci = (-Pr * Theta_Fi / (Pr + 1) +
                   Theta_Fi - theta_Pr / (Pr + 1)) * ci
    elif var == 'nj':
        if fall_type == 'fall':
            dci = (kf * theta_Pr / (V * kinf * (Pr + 1))) * \
                (Fi * (Pr * Theta_Fi + 1) - ci)
        elif fall_type == 'chem':
            dci = kf * theta_Pr * (Fi * Theta_Fi - ci) / (kinf * V * (Pr + 1))
    elif var == 'V':
        if fall_type == 'fall':
            dci = Fi * theta_Pr / (Pr + 1) + (-Pr * Theta_Pr / (Pr + 1) + Theta_Fi +
                                              Theta_Pr - theta_Pr / (Pr + 1)) * ci
        elif fall_type == 'chem':
            dci = (-Pr * Theta_Pr / (Pr + 1) +
                   Theta_Fi - theta_Pr / (Pr + 1)) * ci
    elif var == 'P':
        if fall_type == 'fall':
            dci = Fi * theta_Pr / (Pr + 1) + \
                (Theta_Fi - theta_Pr / (Pr + 1)) * ci
        elif fall_type == 'chem':
            dci = (Theta_Fi - theta_Pr / (Pr + 1)) * ci
    return Xi, dci


oploop = OptionLoop({'fall_type': ['chem', 'fall'],
                     'blend_type': ['lind', 'troe', 'sri'],
                     'pr_type': ['mix', 'unity', 'spec'],
                     'var': ['T', 'nj', 'V', 'P']})

for i, state in enumerate(oploop):
    term_dict = {}
    Xi, dci = __get_dci(**state)

    def __rec_subs(term, depth=0):
        if term.has(Xi):
            ttype = type(term)

            def __separate(args):
                has = []
                hasnt = []
                for a in args:
                    (has if a.has(Xi) else hasnt).append(a)
                return has, hasnt

            def __apply():
                has, hasnt = __separate(ttype.make_args(term))
                return ttype(*[ttype(*[__rec_subs(h) for h in has]),
                               __rec_subs(ttype(*hasnt))])

            if ttype == Pow:
                return Pow(__rec_subs(term.args[0]),
                           __rec_subs(term.args[1]))
            elif ttype == Symbol:
                return term
            elif ttype == log:
                return log(__rec_subs(term.args[0]))
            return __apply()
        else:
            term = simplify(term)
        return term

    dci = __rec_subs(dci)
    print(state)
    print('dci:', dci)
    lim = Limit(dci, Xi, 0, '+').doit(deep=True)
    print('lim:', lim)
    for term, cse in term_dict.iteritems():
        if lim.has(cse):
            lim = lim.subs(cse, term)
    print('lim:', lim)

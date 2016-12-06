from argparse import ArgumentParser
from .derivations import filer, equation_file, derivation

if __name__ == '__main__':
    from argparse import ArgumentParser
    parser = ArgumentParser(description='generates derivations for SPyJac')
    parser.add_argument('-conv', '--constant_volume',
                         action='store_true',
                         default=False)

    args = parser.parse_args()
    conv = args.constant_volume

    with filer('con{}_derivation.tex'.format('v' if conv else 'p'), 'w') as file:
        with equation_file('con{}_derivation.sympy'.format('v' if conv else 'p'), 'w') as efile:
            derivation(file, efile, not conv, True)

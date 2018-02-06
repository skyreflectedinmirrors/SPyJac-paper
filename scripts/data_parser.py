import collections
import os
import yaml

rundata = collections.namedtuple(
    'data', 'num_conditions comptime overhead runtime')
mechdata = collections.namedtuple('mechdata', 'mech num_species num_reactions')
run = collections.namedtuple(
    'run',
    'type sparse lang vecwidth order vectype platform rates kernel cores conp'
    'rundata mechdata')


def parse_data(directory='performance'):
    # find all mechs
    mechs = [x for x in os.listdir(directory)
             if os.path.isdir(os.path.join(directory, x))]
    perf_data = {}
    for mech in mechs:
        perf_data[mech] = []
        path = os.path.join(directory, mech)
        # get files
        files = [os.path.join(path, x) for x in os.listdir(path)]
        files = [x for x in files if os.path.isfile(x)]
        # read mechanism info
        mech_meta_file = next(x for x in files if x.endswith('.yaml'))
        with open(mech_meta_file, 'r') as f:
            mech_info = mechdata(**yaml.load(f))
        files.remove(mech_meta_file)
        for file in files:
            # get name
            name = os.path.basename(file)
            # get run parameters
            params = name[:name.index('.txt')].split('_')
            if params[0] == 'spec':
                # insert 'sparse' type
                params.insert('sparse', 1)
            # get data
            with open(file, 'r') as f:
                lines = [[float(x) for x in l.strip().split(',')]
                         for l in f.readlines() if l.strip()]
            datalist = [rundata(*x) for x in lines]
            # add to run
            params.extend([datalist, mech_info])
            perf_data[mech].append(run(*params))

    return perf_data

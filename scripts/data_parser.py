import collections
import os
import yaml
import hashlib
import pickle

rundata = collections.namedtuple(
    'rundata', 'num_conditions comptime overhead runtime')
mechdata = collections.namedtuple(
    'mechdata', 'mech n_species n_reactions n_reversible')
run = collections.namedtuple(
    'run',
    tuple('rtype sparse lang vecwidth order vectype platform rates kernel cores '
          'conp descriptor rundata mechdata'.split()))

script_dir = os.path.dirname(os.path.normpath(__file__))


def md5sum(filename, blocksize=65536):
    hash = hashlib.md5()
    with open(filename, "rb") as f:
        for block in iter(lambda: f.read(blocksize), b""):
            hash.update(block)
    return hash.hexdigest()


def __listdir(path, files=True, endswith=''):
    plist = [os.path.join(path, x) for x in os.listdir(path)]
    plist = [x for x in plist if os.path.isfile(x) == files]
    if endswith:
        plist = [x for x in plist if x.endswith(endswith)]
    return plist


def files_in(path, endswith='.txt'):
    return __listdir(path, endswith=endswith)


def dirs_in(path):
    return __listdir(path, False)


def parse_data(directory=os.path.join(script_dir, 'performance')):
    # find all mechs
    mechs = [x for x in os.listdir(directory)
             if os.path.isdir(os.path.join(directory, x))]
    perf_data = {}
    for mech in mechs:
        perf_data[mech] = []
        path = os.path.join(directory, mech)
        mech_meta_file = next(x for x in files_in(path, '.yaml'))
        # read mechanism info
        with open(mech_meta_file, 'r') as f:
            mech_info = mechdata(**yaml.load(f))
        for desc in dirs_in(path):
            # get decriptor
            descriptor = os.path.basename(os.path.normpath(desc))
            for file in files_in(desc):
                # check for pickled data
                pickle_file = file.replace('.txt', '.pickle')
                md5_file = file.replace('.txt', '.md5')
                if os.path.isfile(pickle_file) and os.path.isfile(md5_file):
                    # check checksum
                    with open(md5_file, 'r') as md5:
                        stored = md5.read()
                    if md5sum(file) == stored:
                        try:
                            with open(pickle_file, 'rb') as pickled:
                                perf_data[mech].append(pickle.load(pickled))
                                continue
                        except EOFError:
                            pass

                # get name
                name = os.path.basename(file)
                # get run parameters
                params = name[:name.index('.txt')].split('_')
                if params[0] == 'spec':
                    # insert 'sparse' type
                    params.insert(1, 'full')
                # get data
                with open(file, 'r', errors='ignore') as f:
                    lines = f.readlines()
                data = []
                for line in lines:
                    try:
                        floats = [float(x) for x in line.strip().split(',')]
                        data.append(rundata(*floats))
                    except ValueError:
                        # from OpenCL compilation output
                        pass
                # add to run
                params.extend([descriptor, data, mech_info])
                perf_data[mech].append(run(*params))

                # get file checksum and pickle
                checksum = md5sum(file)
                with open(md5_file, 'w') as output:
                    output.write(checksum)

                with open(pickle_file, 'wb') as output:
                    pickle.dump(perf_data[mech][-1], output)

    return perf_data

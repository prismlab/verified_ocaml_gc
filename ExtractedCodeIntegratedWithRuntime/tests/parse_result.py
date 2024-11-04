import csv
from collections import defaultdict
import matplotlib.pyplot as plt
import argparse

parser = argparse.ArgumentParser(
                    prog='Hyperfine Result Parser',
                    description='',
                    epilog='')
parser.add_argument('-s', '--skip')
parser.add_argument('-i', '--input_file')
parser.add_argument('-o', '--output_file')
parser.add_argument('-x', '--xlabel')
parser.add_argument('-y', '--ylabel')
parser.add_argument('-p', '--param_name')

args = parser.parse_args()

assert(args.input_file is not None)
assert(args.output_file is not None)
input_file = args.input_file
output_file = args.output_file
skip = int('0' if args.skip is None else args.skip)
xlabel = "X" if args.xlabel is None else args.xlabel
ylabel = "Y" if args.ylabel is None else args.ylabel
param = "Param" if args.param_name is None else args.param_name



mp = defaultdict(lambda: [])
with open(input_file, newline='') as csvfile:
    reader = csv.reader(csvfile, delimiter=',', quotechar='|')
    all_rows = [line for line in reader]
    for row in all_rows[1:]:
        cmd = row[0].split()
        mp[cmd[0]].append(( int(cmd[-1]), float( row[1] )) )

keys = sorted(list( mp.keys() ))
datas = []

times= []
parameter = []
for key in keys:
    data = sorted( mp[key])[skip:]
    X = list(map(lambda x: x[0],data))
    Y = list(map(lambda x: x[1], data))
    if(len( parameter )==0):
        parameter = X
    else:
        # Sanity check to ensure everything has same labels
        assert(parameter == X)
    times.append(Y)
    plt.plot(X,Y , label=key)

csv_content = []
csv_content.append( param + "," + ",".join( keys ))
for i in range(len(parameter)):
    csv_content.append( ",".join(map(str, [parameter[i]] + [ times[j][i] for j in range(len( keys )) ]))  )
csv_content = list( map(lambda x : x+ "\n", csv_content) )

open(output_file, "w").writelines(csv_content)

plt.xlabel(xlabel)
plt.ylabel(ylabel)
plt.legend()

plt.show()

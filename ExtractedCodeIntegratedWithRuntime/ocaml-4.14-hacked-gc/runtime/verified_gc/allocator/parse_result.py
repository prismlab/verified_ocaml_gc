import csv
from collections import defaultdict
import sys
import matplotlib.pyplot as plt

input_file = sys.argv[1]
output_file = sys.argv[2]
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
depth = []
for key in keys:
    data = sorted( mp[key])[3:]
    X = list(map(lambda x: x[0],data))
    Y = list(map(lambda x: x[1], data))
    if(len( depth )==0):
        depth = X
    times.append(Y)
    plt.plot(X,Y , label=key)

csv_content = []
csv_content.append( "Depth," + ",".join( keys ))
for i in range(len(depth)):
    csv_content.append( ",".join(map(str, [ depth[i], times[0][i], times[1][i], times[2][i]  ]))  )
csv_content = list( map(lambda x : x+ "\n", csv_content) )

open(output_file, "w").writelines(csv_content)

plt.xlabel("Binary Tree Depth")
plt.ylabel("Time Taken")
plt.legend()

plt.show()

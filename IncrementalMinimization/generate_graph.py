import matplotlib.pyplot as pyplot
import sys

xAxis = "Number of States"
yAxis = "Average Minimization Time (ns)"
title = "Comparison of SFA Minimization Algorithms"

testsfile = sys.argv[1]
xIndex = int(sys.argv[2])
graph_indices = [int(i) for i in sys.argv[3:-1]]
cutoff = int(sys.argv[-1])

def toNum(s):
    if s.isdigit():
        return int(s)
    else:
        return float(s)

def mergeData(data, index):
    data.sort(key = lambda x: x[index])
    new_data = []
    count = 1
    for row in data:
        if new_data and new_data[-1][index] == row[index]:
            old_row = new_data[-1]
	    count += 1
            for i in range(0, len(old_row)):
                if i != index:
                    old_row[i] += (row[i] - old_row[i])/float(count) #running average
        else:
            count = 1
            new_data.append(row)
    return new_data
        
with open(testsfile, "r") as f:
    fStrings = f.read().split('\n')

title_row = fStrings[0].split(',')
fData = [[toNum(datum) for datum in row.split(',') if datum]
         for row in fStrings[1:] if row]
fData = mergeData(fData, xIndex)

xData = [row[xIndex] for row in fData if row[xIndex] <= cutoff]
for i in graph_indices:
    graphData = [row[i] for row in fData[:len(xData)]]
    pyplot.plot(xData, graphData, label=title_row[i], linewidth=1.0)
pyplot.yscale("log")
pyplot.legend(loc=0)
pyplot.xlabel(xAxis)
pyplot.ylabel(yAxis)
pyplot.title(title)
pyplot.savefig("graph.png", dpi=600)


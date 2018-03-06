import numpy
import matplotlib.pyplot as pyplot
import matplotlib.colors as colors

import sys

xAxis = "Percentage of Automata Minimized"
yAxis = "Number of States"
title = "Progress of Naive Incremental Minimization"

testsfile = sys.argv[1]

def toNum(s):
    if s.isdigit():
        return int(s)
    else:
        return float(s)

with open(testsfile, "r") as f:
    fStrings = f.read().split("\n")

title_row = fStrings[0].split(',')
x = [toNum(s) for s in title_row[1:-1] if s]

y = []
z = []
index = 0
dataDict = {}
for row in fStrings[1:]:
    if row:
        row = row.split(",")
        states = toNum(row[0])
	maxTime = toNum(row[-2])
        for time in row[1:-1]:
            percent = toNum(time)/maxTime*100
            z.append(percent)
            y.append(states)


x = abs(numpy.unique(x))
y = abs(numpy.unique(y))
X,Y = numpy.meshgrid(x,y)
z = abs(numpy.array(z))
Z = z.reshape(len(y),len(x))
print(Z)
pyplot.pcolormesh(X,Y,Z)
bar = pyplot.colorbar()
bar.set_label("Percentage of Time Passed")

pyplot.title(title)
pyplot.ylabel(yAxis)
pyplot.xlabel(xAxis)
pyplot.xticks(range(0,101,10),["{}%".format(str(int(p)*10)) for p in title_row[1:-1]])
pyplot.savefig("heatmap.png", dpi=600)

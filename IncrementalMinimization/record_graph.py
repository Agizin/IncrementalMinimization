import numpy
import matplotlib.pyplot as pyplot
import plotly.plotly as plotly
import plotly.tools as plottls

import sys

xAxis = "Percentage of Time Passed"
yAxis = "Number of States"
title = "Progress of Symbolic Incremental Minimization"

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
for row in fStrings[1:]:
    if row:
        row = row.split(",")
        print(row)
        states = toNum(row[0])
        for percent in row[1:-1]:
            z.append(toNum(percent))
            y.append(states)


x = numpy.unique(x)
y = numpy.unique(y)
X,Y = numpy.meshgrid(x,y)
z = numpy.array(z)
Z = z.reshape(len(y),len(x))
print(y)
print(x)
print(Z)
pyplot.pcolormesh(X,Y,Z)
bar = pyplot.colorbar()
bar.set_label("Percentage of Minimization Completed")

"""

fig = pyplot.figure()
ax = fig.add_subplot(111)
ax.set_title(title)
plotly_fig = plottls.mpl_to_plotly(fig)
"""

"""
hexbins = pyplot.hexbin(x,y, gridsize=100, cmap = 'inferno')
pyplot.axis([xmin, xmax, ymin, ymax])
colorbar = pyplot.colorbar(hexbins)
"""

pyplot.title(title)
pyplot.ylabel(yAxis)
pyplot.xlabel(xAxis)
pyplot.xticks(range(0,110,10),["{}%".format(p) for p in title_row[1:-1]])
pyplot.savefig("heatmap.png", dpi=600)

import matplotlib.pyplot as pyplot
import matplotlib.ticker as mtick

import sys

xAxis = "Number of States"
yAxis = "Average Amount of Minimization Completed"
title = "Comparison of Incremental Minimization Rates"

testsfile = sys.argv[1]
xIndex = int(sys.argv[2])
percent1_index = int(sys.argv[3])
percent2_index = int(sys.argv[4])
percent3_index = int(sys.argv[5]) #TODO: generalize to arbitrary number of indices
increment = int(sys.argv[6])
cutoff = int(sys.argv[7])

def toNum(s):
    if s.isdigit():
        return int(s)
    else:
        return float(s)

def generate_data(data, increment, cutoff):
    def format_tick(start, end):
        return "{} - {}".format(start, end)
    
    def get_tick_from_point(point):
        mod = int(point) % increment
        start = point - mod
        return format_tick(start, start+increment-1)

    data.sort(key = lambda r: r[xIndex])
    ticks = []
    tick_map = {}
    p1_data = []
    p2_data = []
    p3_data = []
    for i in range(0, cutoff, increment):
        tick_start = i
        tick_end = (i + increment) - 1
        ticks.append(format_tick(tick_start, tick_end))
    cur_index = 0
    count = 1
    for row in range(0, len(data)):
        x = data[row][xIndex]
        if x >= cutoff:
            break
        p1 = data[row][percent1_index]
        p2 = data[row][percent2_index]
        p3 = data[row][percent3_index]
        tick = ticks[cur_index]
        actual_tick = get_tick_from_point(x)
        while(tick != actual_tick):
            cur_index += 1
            if len(p1_data) < cur_index:
                raise NotImplementedError() #TODO: implement if no data in range
            tick = ticks[cur_index]
        if len(p1_data) == cur_index:
            count = 1
            p1_data.append(p1)
            p2_data.append(p2)
            p3_data.append(p3)
        else:
            count += 1
            p1_data[cur_index] += (p1 - p1_data[cur_index])/float(count)
            p2_data[cur_index] += (p2 - p2_data[cur_index])/float(count)
            p3_data[cur_index] += (p3 - p3_data[cur_index])/float(count)
    assert(len(ticks) == len(p1_data))
    assert(len(p1_data) == len(p2_data))
    return ticks, p1_data, p2_data, p3_data

with open(testsfile, "r") as f:
    fStrings = f.read().split('\n')

title_row = fStrings[0].split(',')
fData = [[toNum(datum) for datum in row.split(',') if datum]
         for row in fStrings[1:] if row]

ticks, p1_data, p2_data, p3_data = generate_data(fData, increment, cutoff)

p1_data = [p1*100 for p1 in p1_data]
p2_data = [p2*100 for p2 in p2_data]
p3_data = [p3*100 for p3 in p3_data]
fig, ax = pyplot.subplots(1,1)
percent_format = mtick.FormatStrFormatter("%.0f%%")
ax.bar([a - 0.20 for a in range(0,len(p1_data))], p1_data, width=0.20, label="Efficient Incremental")
ax.bar([b + 0.0 for b in range(0,len(p2_data))], p2_data, width=0.20, label="Naive Incremental")
ax.bar([c + 0.20 for c in range(0,len(p3_data))], p3_data, width=0.20, label ="Incremental with Dependency Check")
pyplot.xticks(range(0, len(ticks)), ticks, fontsize=6)
ax.yaxis.set_major_formatter(percent_format)
pyplot.xlabel(xAxis)
pyplot.ylabel(yAxis)
pyplot.title(title)
pyplot.legend(loc=0)
pyplot.savefig("budget_graph.png", dpi=600)



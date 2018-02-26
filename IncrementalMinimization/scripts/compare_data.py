import sys

file1 = sys.argv[1]
file2 = sys.argv[2]
base_index = int(sys.argv[3])
comp_index = int(sys.argv[4])

def toNum(s):
    if s.isdigit():
        return int(s)
    else:
        return float(s)

with open(file1, "r") as f:
    f1 = f.read().split("\n")

with open(file2, "r") as f:
    f2 = f.read().split("\n")

title_row = f1[0].split(',')
#assert(all(title1 == title2 for title1, title2 in zip(title_row, f2[0].split(','))))
f1Data = [[toNum(datum) for datum in row.split(',') if datum]
          for row in f1[1:] if row]
f2Data = [[toNum(datum) for datum in row.split(',') if datum]
          for row in f2[1:] if row]

good = 0
bad = 0
for row in f1Data:
    if row[0] > 50 and row[1] < 150 and row[0] == row[1]:
        if row[5] <= row[6]:
            good += 1
        else:
            bad +=1
print(good)
print(bad)
            

f1Average = 0
f2Average = 0
f1Min = max([row[base_index] for row in f1Data])
print("adsadad")
f1Max = 0
negs = []
count = 0.0
for row in range(0,min(len(f1Data),len(f2Data))):
    if f1Data[row][0] < 50:
        continue
    count += 1
    if f1Data[row][:4] != f2Data[row][:4]:
        if len(f1Data) > len(f2Data):
            f1Data.pop(row)
        elif len(f1Data) < len(f2Data):
            f2Data.pop(row)
        else:
            raise Exception("Data tables not expressing same data")
            
    f1Comp = f1Data[row][base_index] - f1Data[row][comp_index]
    f2Comp = f2Data[row][base_index] - f2Data[row][comp_index]
    if f1Comp < f1Min:
        f1Min = f1Comp
    if f1Comp > f1Max:
        f1Max = f1Comp
    if f1Comp <= 0:
        negs.append(f1Data[row])
    if count == 0:
        f1Average = f1Comp
        f2Average = f2Comp
    else:
        count += 1.0
        f1Average += (f1Comp - f1Average)/count
        f2Average += (f2Comp - f2Average)/count
        
for n in negs:
    print n
print('avg')
print(f1Average)
print('min')
print(f1Min)
print('max')
print(f1Max)
print(count)

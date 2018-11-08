import numpy
import requests
import sys

def stats(dicts, benchmarks):
    stds = []
    minmax = []    
    for bm in benchmarks:
        res = dicts[0][bm][0]
        times = []

        for d in dicts:
            (r, t) = d[bm]            
            if r != res:
                print("DIFFERENT RESULTS!")
            times.append(t)

        if (res == "SAT" or res == "UNSAT"):
            s = numpy.std(times)
            mm = (max(times) - min(times))/numpy.mean(times)
            minmax.append(mm)

            print("%s" % bm)
            print("\ttimes:\t%s" % times)
            print("\tminmax:\t%f" % mm)
            print("\tstd:\t%f" % s)            
            stds.append(s)

    print("Max std: %f" % max(stds))
    print("Avg std: %f" % numpy.mean(stds))
    print("Max minmax: %f" % max(minmax))
    print("Avg minmax: %f" % numpy.mean(minmax))    

def getJSON(id):
    json = requests.get("http://130.238.29.80/experiments/" + id).json()
    return json

def extractBenchmarks(json):
    benchmarks = []
    for res in json['results']:
        benchmarks.append(res['benchmark'])
    return benchmarks
    

def jsonsToDicts(jsons, benchmarks):
    dicts = []
    for j in jsons:
        d = {}
        for r in j['results']:
            d[r['benchmark']] = (r['result'], r['runtime'])
        dicts.append(d)
    return dicts

def jsonToDict(json):
    d = {}
    for r in json['results']:
        d[r['benchmark']] = (r['result'], r['runtime'])
    return d

def loadInput(file):
    f = open(file, "r")

    data = []

    benchmarks = []

    for line in f:
        sp = line.split()
        desc = sp[0]
        json = getJSON(sp[1])
        benchmarks = extractBenchmarks(json)        
        dict = jsonToDict(json)
        data.append((desc, dict))

    return (data, benchmarks)

def compare(descriptions, dicts, benchmarks):
    for i in range(len(descriptions)):
        print(descriptions[i])
    


def table(benchmarks, data):
    print("<html>")
    print("<table border=\"1\">")
    dicts = []
    descs = []
    for (desc, dict) in data:
        dicts.append(dict)
        descs.append(desc)

    header = "<tr><td>Benchmarks</td>"
    for d in descs:
        header += "<td>" + d + "</td>"
    header += "</tr>"
    print(header)
    for b in benchmarks:
        best = 0
        besttime = dicts[0][b][1]
        for i in range(len(dicts)):
            (res, time) = dicts[i][b]
            if (time < besttime):
                besttime = time
                best = i
        
        body = "<tr>"
        body += "<td>" + b + "</td>"
        results = []
        for i in range(len(dicts)):
            (res, time) = dicts[i][b]
            results.append(res)
            center = ""
            if res == "TIMEOUT":
                center = "t/o"
            elif res == "SAT" or res == "UNSAT":
                center = str(time)
            else:
                center = "!!!"
            if i == best:
                body += "<td><b>" + center + "</b></td>"
            else:
                body += "<td>" + center + "</td>"                
        body += "</tr>"
        # We could add sanitycheck here of results        
        print(body)
    print("</table>")
    print("</html>")        

# print("//--- Analyzing ---\\\\")
infile = sys.argv[1]
# print(infile)
# print("----------------------")
(data, benchmarks) = loadInput(infile)
dicts = []
for (desc, dict) in data:
    dicts.append(dict)
# table(benchmarks, data)
# dicts = jsonsToDicts(jsons, benchmarks)
stats(dicts, benchmarks)

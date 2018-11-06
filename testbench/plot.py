import numpy
import requests
import sys

def std(dicts, benchmarks):
    stds = []
    print(benchmarks)
    for bm in benchmarks:
        res = dicts[0][bm][0]
        times = []

        for d in dicts:
            (r, t) = d[bm]            
            if r != res:
                print("DIFFERENT RESULTS!")
            times.append(t)

        if (res == "SAT" or res == "UNSAT"):
            stds.append(numpy.std(times))

    print(stds)
    print("Max std: %f" % max(stds))
    print("Avg std: %f" % numpy.mean(stds))


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


print("//--- Analyzing ---\\\\")
ids = sys.argv[1:]
jsons = []
for id in ids:
    print(id)
    json = getJSON(id)
    jsons.append(json)
    print(json)
print("----------------------")
benchmarks = extractBenchmarks(jsons[0])
dicts = jsonsToDicts(jsons, benchmarks)
std(dicts, benchmarks)

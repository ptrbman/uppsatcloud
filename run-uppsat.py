import sys
import docker
from docker import APIClient
import datetime

def convert(str):
    s = str.split(".")
    newstr = s[0] + "." + s[1][0:6]
    format = '%Y-%m-%dT%H:%M:%S.%f'    
    return(datetime.datetime.strptime(newstr, format))

def uppsat(benchmark):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()
    
    # Here we have an absolute path
    benchVolume = {'/benchmarks' : {'bind' : '/benchmarks', 'mode' : 'ro'} }
    
    container = client.containers.create("backeman/uppsat:z3", benchmark, volumes=benchVolume)
    container.start()
    ex = container.wait()
    
    # CHECK TIME
    asd =apiclient.inspect_container(resource_id=container.id)
    start = asd['State']['StartedAt']
    end = asd['State']['FinishedAt']
    
    runtime = convert(end) - convert(start)
    
    # CHECK ANSWER
    stdout = container.logs(stdout=True)
    output = "UNKNOWN"
    for l in stdout.decode('ascii').splitlines():
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"
            
            
    # WE ARE DONE!        
    print((output, runtime.total_seconds()))
    # except docker.errors.ContainerError:


print("//==========\\\\")
print("||  UppSAT  ||")
print("\\\\==========//")
     
input=sys.argv[1]
print("Input: " + input)
uppsat(input)

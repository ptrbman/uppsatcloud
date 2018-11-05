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
    log.info("Running UppSAT on benchmark {}".format(benchmark))

    client.login(username="backeman", password="uppsat")

    client.images.pull("backeman/uppsat:z3")

    # Here we have an absolute path
    benchVolume = {'data-volume': {'bind': BENCHMARK_ROOT, 'mode': 'ro'}}
    env = {'INPUT' : "/benchmarks/" + benchmark, 'TIMEOUT' : '10'}    

    container = client.containers.create(
        "backeman/uppsat:z3",
        os.path.join(BENCHMARK_ROOT, benchmark),
        volumes=benchVolume)
    container.start()
    ex = container.wait()

    # CHECK TIME
    asd = apiclient.inspect_container(resource_id=container.id)
    start = asd['State']['StartedAt']
    end = asd['State']['FinishedAt']

    runtime = dateparser.parse(end) - dateparser.parse(start)

    # CHECK ANSWER
    stdout = container.logs(stdout=True)
    output = "UNKNOWN"
    for l in stdout.decode('ascii').splitlines():
        log.info(l)
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"

    # Maybe exception handling...
    # WE ARE DONE!

    log.info("UppSAT: %s %f", output, runtime.total_seconds())
    return (output, runtime.total_seconds())


def uppsat(benchmark):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()

    client.login(username="backeman", password="uppsat")

    client.images.pull("backeman/uppsat:z3")
    
    # Here we have an absolute path
    # benchVolume = {'data-volume' : {'bind' : '/benchmarks', 'mode' : 'ro'} }
    benchVolume = {'/benchmarks' : {'bind' : '/benchmarks', 'mode' : 'ro'} }    
    env = {'INPUT' : "/benchmarks/" + benchmark, 'TIMEOUT' : '10'}

    
    container = client.containers.create("backeman/uppsat:z3", volumes=benchVolume, environment=env)
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
        print(l)
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"
            

    # Maybe exception handling...
    # WE ARE DONE!
    print("UppSAT:")
    print(env)
    print((output, runtime.total_seconds()))
    return (output, runtime.total_seconds())


print("//==========\\\\")
print("||  UppSAT  ||")
print("\\\\==========//")
     
input=sys.argv[1]
print("Input: " + input)
uppsat(input)

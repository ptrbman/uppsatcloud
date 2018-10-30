echo "Installing docker"
sudo apt-get -y update
sudo apt-get -y  install \
    apt-transport-https \
    ca-certificates \
    curl \
    software-properties-common
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo apt-key add -
sudo add-apt-repository -y  \
   "deb [arch=amd64] https://download.docker.com/linux/ubuntu \
   $(lsb_release -cs) \
   stable"
sudo apt-get  -y update
sudo apt-get  -y install docker-ce

sudo groupadd docker
sudo usermod -aG docker ubuntu

exec su -l ptr

sudo docker run hello-world
sudo docker login -u backeman -p uppsat
sudo docker pull backeman/uppsat:z3

sudo apt -y install python3-venv
sudo apt -y install python3-pip

python3 -m venv pydocker
source pydocker/bin/activate
pip install docker

#sudo docker run -v /home/root/benchmarks:/benchmarks /benchmarks/...

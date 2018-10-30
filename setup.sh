echo "Installing docker"
sudo apt-get --force-yes update
sudo apt-get --force-yes  install \
    apt-transport-https \
    ca-certificates \
    curl \
    software-properties-common
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo apt-key add -
sudo add-apt-repository --force-yes  \
   "deb [arch=amd64] https://download.docker.com/linux/ubuntu \
   $(lsb_release -cs) \
   stable"
sudo apt-get  --force-yes update
sudo apt-get  --force-yes install docker-ce

sudo groupadd docker
sudo usermod -aG docker ubuntu


sudo docker run hello-world
sudo docker login -u backeman -p uppsat
sudo docker pull backeman/uppsat:z3

#sudo docker run -v /home/root/benchmarks:/benchmarks /benchmarks/...

pip install docker

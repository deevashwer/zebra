# install essential tools
sudo yum groupinstall "Development Tools"
sudo apt install build-essential

# install go
wget https://dl.google.com/go/go1.20.4.linux-amd64.tar.gz
sudo rm -rf /usr/local/go && sudo tar -C /usr/local -xzf go1.20.4.linux-amd64.tar.gz
echo "export PATH=$PATH:/usr/local/go/bin" >> ~/.bashrc
source ~/.bashrc
rm go1.20.4.linux-amd64.tar.gz
# setup go dependences
go mod tidy

# install npm
wget -qO- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.1/install.sh | bash
source ~/.bashrc
nvm install 20.0.0
# setup npm dependences
npm install
cd contract && npm install && cd ..

# install rust
curl https://sh.rustup.rs -sSf | sh
source ~/.bashrc

# install circom
git clone https://github.com/iden3/circom.git
cd circom
cargo build --release
cargo install --path circom
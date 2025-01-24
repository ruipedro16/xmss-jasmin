FROM debian:stable-20250113-slim

LABEL version="0.0.1"
LABEL maintainer="rui.fernandes@mpi-sp.org" 

ARG USER="xmss-user"

# We use the commit instead of the release because jasmin2ec is not available in the release,
# but we need it extract Jasmin source code to EasyCrypt.
# Este commit corresponde ao release. 
# Este commit vem do gitlab https://gitlab.com/jasmin-lang/jasmin-compiler
ARG JASMIN_COMMIT=46ef1f3af0ab5b988a2149f2d384ed1f2f4d18d9 
ARG EASYCRYPT_COMMIT=d03e63d21618db2a0cb09d0a0770f5e774dd6c74 

SHELL ["/bin/bash", "-c"]

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install \
      sudo wget curl git time xz-utils libicu-dev \
      ocaml ocaml-native-compilers camlp4-extra opam \
      autoconf debianutils libgmp-dev pkg-config zlib1g-dev \
      vim build-essential python3 python3-pip m4 libgsl-dev \ 
      libpcre3-dev jq parallel valgrind bash-completion \
      libtext-diff-perl

RUN apt-get --quiet --assume-yes clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd --create-home --shell /bin/bash --home-dir /home/$USER --user-group --groups sudo --uid 1001 $USER

USER $USER
WORKDIR /home/$USER

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install

# Install EasyCrypt & SMT Solvers
RUN export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam init --disable-sandboxing && \
    opam install opam-depext && \
    opam pin add -n alt-ergo 2.5.2 && \
    opam install alt-ergo && \
    opam clean

RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
      -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \ 
    sudo install -D cvc4 /usr/local/bin/

RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
    https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip && \
    unzip -j z3-4.13.0-x64-glibc-2.35.zip z3-4.13.0-x64-glibc-2.35/bin/z3 && \
    sudo install -D z3 /usr/local/bin/

RUN eval $(opam env) && \
    export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam pin -n add easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_COMMIT} && \ 
    opam depext easycrypt && \
    opam install easycrypt && \
    easycrypt why3config

# Install Jasmin
RUN git clone https://github.com/jasmin-lang/jasmin.git && \
    cd jasmin && \    
    git checkout $JASMIN_COMMIT && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    nix-shell --command "(cd compiler && make clean && make CIL && make)" && \
    sudo install -D compiler/jasmin* /usr/local/bin/ && \
    cd - && echo -e "[general]\nidirs = Jasmin:$(pwd)/jasmin/eclib" > ~/.config/easycrypt/easycrypt.conf

COPY --chown=$USER:$USER . /home/$USER/xmss-jasmin
WORKDIR /home/$USER/xmss-jasmin

RUN echo 'eval $(opam env)' >> /home/$USER/.bashrc
CMD ["bash"]

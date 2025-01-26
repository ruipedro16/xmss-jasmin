FROM debian:stable-20250113-slim

LABEL version="0.0.1"
LABEL maintainer="rui.fernandes@mpi-sp.org" 

# See https://stackoverflow.com/questions/72583938/redundant-eval-opam-env-needed-in-dockerfile and
# https://stackoverflow.com/questions/70888834/run-bash-then-eval-command-on-docker-container-startup?noredirect=1&lq=1

ARG USER="xmss-user"

# Obs:
#
# We build Jasmin from the Gitlab because it is faster as we dont have to deal with the Coq stuff
# We build it from a specific commit instead of using a release because the releases do not have
# jasmin2ec
#
# We get EClib from Github instead of the Gitlab because I dont know the equivalent commit in the
# Gitlab (FIXME: TODO: This could be fixed so we get the compiler & jasminc, jasmin-ct and jasmmin2ec
# from the same place)
# 
# We use this specific commit instead of the latest because the proofs do not check with 
# the latest ECLib 
#

ARG ECLIB_COMMIT=46ef1f3af0ab5b988a2149f2d384ed1f2f4d18d9 
ARG JASMIN_COMMIT=c194e7b268c36b90fe39e6a30131b618a9e4fd1a
ARG EASYCRYPT_COMMIT=d03e63d21618db2a0cb09d0a0770f5e774dd6c74 

SHELL ["/bin/bash", "-c"]

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

# Download ECLib
RUN git clone https://github.com/jasmin-lang/jasmin.git jasmin-eclib && \
    cd jasmin-eclib && \    
    git checkout $ECLIB_COMMIT && \
    echo -e "[general]\nidirs = Jasmin:$(pwd)/eclib" > ~/.config/easycrypt/easycrypt.conf

# Install Jasmin
RUN git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git jasmin-compiler && \
    cd jasmin-compiler && \
    git checkout $JASMIN_COMMIT && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    cd compiler/ && nix-shell --command "make" && \
    sudo install -D jasmin* /usr/local/bin/

COPY --chown=$USER:$USER . /home/$USER/xmss-jasmin
WORKDIR /home/$USER/xmss-jasmin

ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]


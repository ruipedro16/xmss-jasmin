FROM debian:stable-slim

LABEL MAINTAINER Rui Fernandes <ruipedro16@protonmail.com>


ENV DEBIAN_FRONTEND=noninteractive

ARG USERNAME=xmss_jasmin

ARG EASYCRYPT_COMMIT=4201fddc14b81d2a69a33f034c9c7db4dfd58d0e
ARG JASMIN_COMMIT=e84c0c59b4f4e005f2be4de5fdfbcaf1e3e2f975
ARG JASMIN_COMPILER_COMMIT=252e602bd76606942d6e1b2aa7d44eb4d09f1712 # corresponding extracted sources on gitlab.com (builds faster)

RUN apt-get -q -y update && apt-get -q -y upgrade && \
    apt-get -q -y install apt-utils sudo wget build-essential curl opam git m4 libgmp-dev libpcre3-dev pkg-config zlib1g-dev cvc4 vim gcc clang && \
    apt-get -q -y clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd -ms /bin/bash -d /home/$USERNAME -g root -G sudo -u 1001 $USERNAME

USER $USERNAME
WORKDIR /home/$USERNAME

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install && \
    (USER=$USERNAME; . /home/$USERNAME/.nix-profile/etc/profile.d/nix.sh) && \
    rm nix-install

# Install EasyCrypt

ENV OPAMYES=true OPAMJOBS=8
ENV ALTERGO=2.4.2 Z3=4.8.14

RUN opam init --disable-sandboxing 

RUN opam pin add -n alt-ergo ${ALTERGO} && \
    opam depext alt-ergo && \
    opam install alt-ergo && \
    opam clean

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3}/z3-${Z3}-x64-glibc-2.31.zip && \
    unzip -j z3-${Z3}-x64-glibc-2.31.zip z3-${Z3}-x64-glibc-2.31/bin/z3 && \
    sudo mv z3 /usr/local/bin/ && sudo chmod 755 /usr/local/bin/z3 && \
    rm -fr z3-${Z3}-x64-glibc-2.31.zip

RUN opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_COMMIT} && \
    opam depext easycrypt && \
    opam install easycrypt && \
    opam clean

RUN opam config exec -- why3 config detect

# Install Jasmin

RUN git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git && \
    cd jasmin-compiler/ && \
    git checkout ${JASMIN_COMPILER_COMMIT}

RUN USER=$USERNAME; . /home/$USERNAME/.nix-profile/etc/profile.d/nix.sh && \
    cd jasmin-compiler/compiler && \
    nix-shell --command "make" && \
    sudo install -D jasminc /usr/local/bin/

RUN git clone https://github.com/jasmin-lang/jasmin.git && \
    cd jasmin/ && \
    git checkout ${JASMIN_COMMIT} && \
    mkdir -p /home/$USERNAME/.config/easycrypt/ && \
    echo "[general]\nidirs = Jasmin:/home/$USERNAME/jasmin/eclib" > /home/$USERNAME/.config/easycrypt/easycrypt.conf

RUN echo "eval $(opam env)" >> /home/$USERNAME/.bashrc

USER $USERNAME
COPY . .
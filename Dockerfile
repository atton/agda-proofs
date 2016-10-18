# docker build -t agda:2.5.1.1 .
# docker run -it agda:2.5.1.1 zsh

FROM fedora:24

RUN dnf update -y
RUN dnf install -y ghc emacs vim mercurial git cabal-install zlib zlib-devel zsh wget tar man
RUN cabal update
RUN cabal install cabal-install
RUN cabal install happy-1.19.5 alex-3.1.7
RUN cabal install --force-reinstalls agda-2.5.1.1

WORKDIR /tmp
RUN mkdir -p /root/.agda/lib
RUN wget https://github.com/agda/agda-stdlib/archive/v0.12.tar.gz
RUN tar xzf v0.12.tar.gz -C /root/.agda/lib
RUN echo "standard-library" >> /root/.agda/defaults
RUN echo "/root/.agda/lib/agda-stdlib-0.12/standard-library.agda-lib" >> /root/.agda/libraries

WORKDIR /root
RUN hg clone http://firefly.cr.ie.u-ryukyu.ac.jp/hg/Members/atton/agda-proofs

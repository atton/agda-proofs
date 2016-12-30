# docker build -t agda:2.5.2 .
# docker run -it agda:2.5.2 zsh

FROM fedora:25

RUN dnf update -y
RUN dnf install -y ghc emacs vim mercurial git cabal-install zlib zlib-devel zsh wget tar man
RUN cabal update
RUN cabal install cabal-install
RUN cabal install happy-1.19.5 alex-3.2.1 cpphs-1.20.2
RUN cabal install --force-reinstalls agda-2.5.2

WORKDIR /tmp
RUN mkdir -p /root/.agda/lib
RUN wget https://github.com/agda/agda-stdlib/archive/v0.13.tar.gz
RUN tar xzf v0.13.tar.gz -C /root/.agda/lib
RUN echo "standard-library" >> /root/.agda/defaults
RUN echo "/root/.agda/lib/agda-stdlib-0.13/standard-library.agda-lib" >> /root/.agda/libraries

WORKDIR /root
RUN hg clone http://firefly.cr.ie.u-ryukyu.ac.jp/hg/Members/atton/agda-proofs

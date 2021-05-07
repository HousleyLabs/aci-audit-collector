FROM python:3.6-slim
ENV PYTHONUNBUFFERED 1

RUN mkdir /housley
WORKDIR /housley/code
COPY requirements.txt /

RUN apt-get update \
    && apt-get install -y wget iputils-ping

# Install build deps, then run `pip install`, then remove unneeded build deps all in a single step.
RUN set -ex && BUILD_DEPS="build-essential libpcre3-dev libpq-dev" \
    && apt-get install -y --no-install-recommends $BUILD_DEPS \
    && pip install -U pip \
    && pip install --no-cache-dir -r /requirements.txt \
    && apt-get purge -y --auto-remove -o APT::AutoRemove::RecommendsImportant=false $BUILD_DEPS \
    && rm -rf /var/lib/apt/lists/*

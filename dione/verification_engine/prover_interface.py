""" Python interface for interacting with proof assistants """

import abc


class ProverInterface(abc.ABC):
    def __init__(self):
        pass

    async def __aenter__(self):
        pass

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        pass

    @abc.abstractmethod
    def verify(self, code):
        pass

    @abc.abstractmethod
    def counter_example(self, code):
        pass

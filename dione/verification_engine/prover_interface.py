""" Python interface for interacting with proof assistants """

import abc


class ProverInterface(abc.ABC):
    def __init__(self):
        pass

    def __enter__(self):
        pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

    @abc.abstractmethod
    def verify(self, code):
        pass

    @abc.abstractmethod
    def counter_example(self, code):
        pass

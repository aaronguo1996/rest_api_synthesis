import numpy as np
import torch

from apiphany.NLP.infrastructure.logger import Logger
from apiphany.NLP.models.bert import Bert

class Trainer:
    def __init__(self, params):
        self.params = params
        self.logger = Logger(self.params['logdir'])

        # set random seeds
        seed = self.params['seed']
        np.random.seed(seed)

        self.model = Bert(params)

    def perform_eval(self):
        sentence1 = "Retrieve members of a conversation"
        sentence2 = "Retrieve emails of all members in a channel"
        score = self.model.similarity(sentence1, sentence2)
        print("sentence 1:", sentence1)
        print("sentence 2:", sentence2)
        print("score:", score)
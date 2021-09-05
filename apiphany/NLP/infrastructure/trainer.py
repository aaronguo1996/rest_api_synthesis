import numpy as np
import pickle
import torch
import torch.nn.functional as F

from apiphany.NLP.infrastructure.logger import Logger
from apiphany.NLP.models.bert import Bert
from apiphany.NLP.infrastructure.utils import plot_probs

class Trainer:
    def __init__(self, params):
        self.params = params
        self.logger = Logger(self.params['logdir'])

        # set random seeds
        seed = self.params['seed']
        np.random.seed(seed)

        self.model = Bert(params)

    def test_similarity(self):
        score = self.model.similarity(
            "Fetch information about settings in a workspace",
            "Retrieve emails of all members in a channel"
        )
        print(score)

        score = self.model.similarity(
            "Retrieve members of a conversation",
            "Retrieve emails of all members in a channel"
        )
        print(score)

        score = self.model.similarity(
            "Set an expiration for a guest user",
            "Retrieve emails of all members in a channel"
        )
        print(score)

    def perform_eval(self):
        apis = ["slack"] #, "stripe", "square"]
        for api in apis:
            with open(f"apiphany/data/nlp_data/{api}_pairs.pkl", "rb") as f:
                pairs = pickle.load(f)
                descriptions = pairs["descriptions"] # list of benchmark descriptions
                components = pairs["components"] # map of component names to component descriptions

                with torch.no_grad():
                    description_encodings = torch.stack([self.model.tokenize(desc) for desc in descriptions])
                    desc_hiddens = self.model(description_encodings).last_hidden_state # N x SENTENCE_LEN x HIDDEN_DIM
                    desc_hiddens = desc_hiddens.reshape((len(descriptions), -1)) # N x (SENTENCE_LEN x HIDDEN_DIM)

                    component_encodings = torch.stack([self.model.tokenize(comp) for comp in components.values()])
                    comp_hiddens = self.model(component_encodings).last_hidden_state # M x SENTENCE_LEN x HIDDEN_DIM
                    comp_hiddens = comp_hiddens.reshape((len(components), -1)) # M x (SENTENCE_LEN x HIDDEN_DIM)

                    print(desc_hiddens.shape)
                    print(desc_hiddens.unsqueeze(1).shape)
                    scores = F.cosine_similarity(desc_hiddens.unsqueeze(1), comp_hiddens, dim=-1) # N x M
                    # scores = []
                    # for i in range(0, len(components), 100):
                    #     part_components = component_encodings[i:i+100]
                    #     part_hiddens = self.model(part_components).last_hidden_state # 100 x (SENTENCE_LEN x HIDDEN_DIM)
                    #     part_hiddens = part_hiddens.reshape((len(part_components), -1))
                    #     part_scores = F.cosine_similarity(desc_hiddens.unsqueeze(1), part_hiddens, dim=-1)
                    #     scores.append(part_scores)

                    # scores = torch.cat(scores, dim=1)
                    # print(scores.shape)
                    # print(scores)
                    # min_indices = torch.argmin(scores, dim=-1, keepdim=True)
                    # print(np.array(list(components.keys()))[min_indices.numpy()], scores[:,min_indices])
                    # scores = F.softmax(scores, dim=-1).detach()

                    # get top 10 for each benchmark
                    for i, score in enumerate(scores):
                        # print(score)
                        top_10_scores, top_10_indices = torch.topk(score, 50)
                        xlabels = np.array(list(components.keys()))[top_10_indices.numpy()]
                        ylabels = [descriptions[i]]
                        print(descriptions[i])
                        for i in top_10_indices:
                            comp_name = list(components.keys())[i]
                            print(comp_name, score[i].item())
                            print(components[comp_name])
                            print()

                        print("===================\n")
                        # plot_probs(f"{api}_{i}.png", top_10_scores.reshape(1,20), xlabels, ylabels)
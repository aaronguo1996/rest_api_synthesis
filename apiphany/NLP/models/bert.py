import torch
import torch.nn as nn

from apiphany.NLP.models.base_model import BaseModel

class Bert(BaseModel):
    def __init__(self, params):
        super().__init__()

        self.params = params

        self.tokenizer = torch.hub.load('huggingface/pytorch-transformers', 'tokenizer', 'bert-base-uncased')    # Download vocabulary from S3 and cache.
        self.model = torch.hub.load('huggingface/pytorch-transformers', 'model', 'bert-base-uncased')    # Download model and configuration from S3 and cache.

    def tokenize(self, sentences):
        return self.tokenizer.encode_plus(
            text = sentences,
            max_length = 64,
            padding = 'max_length',
            return_tensors = 'pt')['input_ids'][0]

    def __call__(self, x):
        return self.model(x)

    def similarity(self, lhs_sentence, rhs_sentence):
        length = max(len(lhs_sentence), len(rhs_sentence))
        lhs_tokens = self.tokenizer.encode_plus(
            text = lhs_sentence, 
            max_length = length, 
            padding = 'max_length',
            return_tensors = 'pt')
        rhs_tokens = self.tokenizer.encode_plus(
            text = rhs_sentence,
            max_length = length, 
            padding = 'max_length',
            return_tensors = 'pt')
        
        lhs_tokens_tensor = lhs_tokens['input_ids']
        rhs_tokens_tensor = rhs_tokens['input_ids']

        with torch.no_grad():
            lhs_outputs = self.model(lhs_tokens_tensor)
            rhs_outputs = self.model(rhs_tokens_tensor)
            
            lhs_encoded_layer = lhs_outputs.last_hidden_state.reshape((1, -1))
            rhs_encoded_layer = rhs_outputs.last_hidden_state.reshape((1, -1))

            # print(lhs_outputs)
            # print(rhs_encoded_layer.shape)

            cos = nn.CosineSimilarity()
            return cos(lhs_encoded_layer, rhs_encoded_layer)
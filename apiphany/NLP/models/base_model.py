class BaseModel:
    def __init__(self, **kwargs):
        super().__init__(**kwargs)

    def train(self):
        raise NotImplementedError

    def similarity(self, sentence1, sentence2):
        raise NotImplementedError
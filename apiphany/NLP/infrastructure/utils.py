import matplotlib.pyplot as plt
import numpy as np

def plot_probs(filename, scores, xlabels, ylabels):
    fig, ax = plt.subplots()
    im = ax.imshow(scores)
    ax.set_xticks(np.arange(len(xlabels)))
    ax.set_yticks(np.arange(len(ylabels)))
    ax.set_xticklabels(xlabels)
    ax.set_yticklabels(ylabels)
    # Rotate the tick labels and set their alignment.
    plt.setp(ax.get_xticklabels(), rotation=45, ha="right",
            rotation_mode="anchor")

    # Loop over data dimensions and create text annotations.
    for j in range(len(ylabels)):
        text = ax.text(j, 0, scores[j],
                    ha="center", va="center", color="w")

    fig.tight_layout()
    plt.savefig(filename)
    plt.close()
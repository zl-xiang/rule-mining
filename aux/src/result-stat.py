import pandas as pd
import re

def compute_stats(csv_path):
    """
    Reads a CSV file and computes mean and std (sample std) for selected columns.

    Parameters:
        csv_path (str): Path to the CSV file

    Returns:
        pd.DataFrame: DataFrame with mean and std for each metric
    """
    
    # Columns to evaluate
    cols = [
        "popper_time_sec",
        "train_precision",
        "train_recall",
        "rules",
        "size",
        "test_precision",
        "test_recall",
        "test_f1"
    ]
    
    # Load data
    df = pd.read_csv(csv_path)
    
    # Ensure numeric (in case CSV has strings)
    df[cols] = df[cols].apply(pd.to_numeric, errors='coerce')
    
    # Compute stats
    mean = df[cols].mean()
    std = df[cols].std(ddof=1)  # sample std (n-1)
    
    # Combine into a single table
    stats_df = pd.DataFrame({
        "mean": mean,
        "std": std
    })
    
    return stats_df



import os
import pandas as pd
import matplotlib.pyplot as plt


import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import scienceplots

def plot_metrics_from_csvs(
    csv_paths,
    columns,
    figsize=(3, 2.5),
    title=None,
    save_path=None,
    variance="std",
    labels = []
    # "std", "sem", or None
):
    """
    Plot mean values of selected columns across multiple CSV files,
    with optional variance regions.

    Parameters
    ----------
    csv_paths : list[str]
        List of CSV file paths.

    columns : list[str]
        Columns to plot.

    figsize : tuple, default=(8, 5)
        Figure size.

    title : str or None
        Plot title.

    save_path : str or None
        Path to save figure.

    variance : str or None, default="std"
        Type of variance region:
            - "std" : mean ± standard deviation
            - "sem" : mean ± standard error
            - None  : no variance region
    """

    # SciencePlots style
    plt.style.use(['science', 'grid', 'vibrant'])

    # Store statistics
    means = {col: [] for col in columns}
    variances = {col: [] for col in columns}

    # X-axis labels
    x_labels = labels

    for path in csv_paths:

        df = pd.read_csv(path)

        # Use filename as label
        if len(x_labels)<1:
            x_labels.append(os.path.basename(path))

        for col in columns:

            if col not in df.columns:
                raise ValueError(f"Column '{col}' not found in {path}")

            # Convert to numeric safely
            values = pd.to_numeric(df[col], errors="coerce").dropna()

            if len(values) == 0:
                raise ValueError(
                    f"No numeric values found in column '{col}' of {path}"
                )

            mean = values.mean()

            if variance == "std":
                var = values.std()

            elif variance == "sem":
                var = values.std() / np.sqrt(len(values))

            else:
                var = 0

            means[col].append(mean)
            variances[col].append(var)

    # X-axis positions
    x = np.arange(len(csv_paths))

    # Plot
    plt.figure(figsize=figsize)

    for col in columns:

        y = np.array(means[col])
        v = np.array(variances[col])

        # Main line
        line = plt.plot(
            x,
            y,
            marker="o",
            linewidth=2,
            label=col,
            color='green'
        )

        # Variance region
        if variance is not None:
            plt.fill_between(
                x,
                y - v,
                y + v,
                alpha=0.2,
                color=line[0].get_color()
            )

    # Formatting
    plt.xticks(x, x_labels, rotation=20)
    plt.xlabel("\\textbf{Percentage of Training Data $(\%)$}")
    plt.ylabel("\\textbf{Learning Time (s)}")
    plt.minorticks_on()

    plt.grid(
        True,
        which="major",
        linestyle="--",
        linewidth=0.6,
        alpha=0.6,
    )

    if title:
        plt.title(title)

    # plt.legend()
    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches=None, pad_inches=0.02,)

    plt.show()


def plot_acc_from_csvs(
    csv_paths,
    columns,
    figsize=(3, 2.5),
    title=None,
    save_path=None,
    variance="std",
    labels = []
    # "std", "sem", or None
):
    """
    Plot mean values of selected columns across multiple CSV files,
    with optional variance regions.

    Parameters
    ----------
    csv_paths : list[str]
        List of CSV file paths.

    columns : list[str]
        Columns to plot.

    figsize : tuple, default=(8, 5)
        Figure size.

    title : str or None
        Plot title.

    save_path : str or None
        Path to save figure.

    variance : str or None, default="std"
        Type of variance region:
            - "std" : mean ± standard deviation
            - "sem" : mean ± standard error
            - None  : no variance region
    """

    # SciencePlots style
    plt.style.use(['science', 'grid', 'vibrant'])

    # Store statistics
    means = {col: [] for col in columns}
    variances = {col: [] for col in columns}

    # X-axis labels
    x_labels = labels

    for path in csv_paths:

        df = pd.read_csv(path)

        # Use filename as label
        if len(x_labels)<1:
            x_labels.append(os.path.basename(path))

        for col in columns:

            if col not in df.columns:
                raise ValueError(f"Column '{col}' not found in {path}")

            # Convert to numeric safely
            values = pd.to_numeric(df[col], errors="coerce").dropna()

            if len(values) == 0:
                raise ValueError(
                    f"No numeric values found in column '{col}' of {path}"
                )

            mean = values.mean()

            if variance == "std":
                var = values.std()

            elif variance == "sem":
                var = values.std() / np.sqrt(len(values))

            else:
                var = 0

            means[col].append(mean)
            variances[col].append(var)

    # X-axis positions
    x = np.arange(len(csv_paths))

    # Plot
    plt.figure(figsize=figsize)
    markers = ['o', 's', '^']
    labels = ['P','R','F1']
    for i,col in enumerate(columns):

        y = np.array(means[col]) * 100
        v = np.array(variances[col]) * 100

        # Main line
        plt.plot(
            x,
            y,
            marker= markers[i],
            linewidth=2,
            label=labels[i],
        )

        # Variance region
        if variance is not None:
            plt.fill_between(
                x,
                y - v,
                y + v,
                alpha=0.2,
            )

    # Formatting
    plt.xticks(x, x_labels, rotation=20)
    plt.xlabel("\\textbf{Percentage of Training Data $(\%)$}")
    plt.ylabel("\\textbf{Avg. Score $(\%)$}")
    plt.minorticks_on()

    plt.grid(
        True,
        which="major",
        linestyle="--",
        linewidth=0.6,
        alpha=0.6,
    )

    if title:
        plt.title(title)

    plt.legend()
    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches="tight")

    plt.show()
    
    
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt


def plot_acc_from_csv_groups(
    csv_groups,
    columns,
    figsize_per_plot=(3, 2.5),
    title=None,
    save_path=None,
    variance="std",
    group_titles=None,
    x_labels_groups=None,
    line_labels=None,
):
    """
    Plot multiple groups of CSV files as separate subplots in one PDF,
    sharing the same legend.

    Parameters
    ----------
    csv_groups : list[list[str]]
        A collection of CSV path lists.
        Each inner list will become one subplot.

    columns : list[str]
        Columns to plot.

    figsize_per_plot : tuple, default=(3, 2.5)
        Size of each subplot.

    title : str or None
        Global figure title.

    save_path : str or None
        Path to save PDF/figure.

    variance : str or None, default="std"
        Type of variance region:
            - "std" : mean ± standard deviation
            - "sem" : mean ± standard error
            - None  : no variance region

    group_titles : list[str] or None
        Titles for each subplot.

    x_labels_groups : list[list[str]] or None
        X-axis labels for each subplot.

    line_labels : list[str] or None
        Labels for plotted columns.
    """

    # Style
    plt.style.use(["science", "grid", "vibrant"])

    n_groups = len(csv_groups)

    if line_labels is None:
        line_labels = columns

    if group_titles is None:
        group_titles = [None] * n_groups

    if x_labels_groups is None:
        x_labels_groups = [None] * n_groups

    # Create figure
    fig_width = figsize_per_plot[0] * n_groups
    fig_height = figsize_per_plot[1]

    fig, axes = plt.subplots(
        1,
        n_groups,
        figsize=(fig_width, fig_height),
        squeeze=False,
    )

    axes = axes.flatten()

    markers = ['o', 's', '^', 'D', 'v', '*']

    shared_handles = None

    # -------------------------------------------------------
    # Draw each subplot
    # -------------------------------------------------------
    for group_idx, csv_paths in enumerate(csv_groups):

        ax = axes[group_idx]

        means = {col: [] for col in columns}
        variances = {col: [] for col in columns}

        x_labels = (
            x_labels_groups[group_idx]
            if x_labels_groups[group_idx] is not None
            else []
        )

        # -----------------------------------------
        # Read CSVs
        # -----------------------------------------
        for path in csv_paths:

            df = pd.read_csv(path)

            if len(x_labels) < len(csv_paths):
                x_labels.append(os.path.basename(path))

            for col in columns:

                if col not in df.columns:
                    raise ValueError(
                        f"Column '{col}' not found in {path}"
                    )

                values = pd.to_numeric(
                    df[col],
                    errors="coerce"
                ).dropna()

                if len(values) == 0:
                    raise ValueError(
                        f"No numeric values found in "
                        f"column '{col}' of {path}"
                    )

                mean = values.mean()

                if variance == "std":
                    var = values.std()

                elif variance == "sem":
                    var = values.std() / np.sqrt(len(values))

                else:
                    var = 0

                means[col].append(mean)
                variances[col].append(var)

        # -----------------------------------------
        # Plot
        # -----------------------------------------
        x = np.arange(len(csv_paths))

        local_handles = []

        for i, col in enumerate(columns):

            y = np.array(means[col]) * 100
            v = np.array(variances[col]) * 100

            line, = ax.plot(
                x,
                y,
                marker=markers[i % len(markers)],
                linewidth=2,
                label=line_labels[i],
            )

            local_handles.append(line)

            if variance is not None:
                ax.fill_between(
                    x,
                    y - v,
                    y + v,
                    alpha=0.2,
                )

        if shared_handles is None:
            shared_handles = local_handles

        # -----------------------------------------
        # Formatting
        # -----------------------------------------
        ax.set_xticks(x)
        ax.set_xticklabels(x_labels, rotation=20)

        ax.set_xlabel(
            r"\textbf{Percentage of Training Data $(\%)$}"
        )

        if group_idx == 0:
            ax.set_ylabel(
                r"\textbf{Avg. Score $(\%)$}"
            )

        ax.minorticks_on()

        ax.grid(
            True,
            which="major",
            linestyle="--",
            linewidth=0.6,
            alpha=0.6,
        )

        if group_titles[group_idx]:
            ax.set_title(group_titles[group_idx])

    # -------------------------------------------------------
    # Shared legend
    # -------------------------------------------------------
    fig.legend(
        handles=shared_handles,
        labels=line_labels,
        loc="upper center",
        ncol=len(line_labels),
        bbox_to_anchor=(0.5, 1.08),
        frameon=True,
    )

    # Global title
    if title:
        fig.suptitle(title, y=1.15)

    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(
            save_path,
            dpi=300,
            bbox_inches="tight",
        )

    plt.show()
    
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import scienceplots


def plot_bar_line_dual_axis(
    csv_paths,
    columns,
    figsize=(3, 3),
    title=None,
    save_path=None,
    variance="std",   # "std", "sem", or None
    scale_left=1.0,
    scale_right=1.0,
):
    """
    Plot dual-axis chart from multiple CSV files.

    Parameters
    ----------
    csv_paths : list[str]
        List of CSV file paths.

    columns : tuple(str, str)
        (bar_column, line_column)

        - first column:
            displayed as bar chart on LEFT y-axis

        - second column:
            displayed as line plot on RIGHT y-axis

    figsize : tuple
        Figure size.

    title : str or None
        Plot title.

    save_path : str or None
        Save figure if provided.

    variance : str or None
        Variance region for line plot:
            - "std"
            - "sem"
            - None

    scale_left : float
        Scale factor for left-axis values.

    scale_right : float
        Scale factor for right-axis values.
    """

    # Style
    plt.style.use(['science', 'vibrant'])

    # Columns
    bar_col, line_col = columns

    # Statistics
    bar_means = []
    line_means = []
    line_vars = []

    # X-axis labels
    x_labels = []

    for path in csv_paths:

        df = pd.read_csv(path)

        x_labels.append(os.path.basename(path))

        # Validate columns
        for col in [bar_col, line_col]:
            if col not in df.columns:
                raise ValueError(f"Column '{col}' not found in {path}")

        # Convert to numeric
        bar_values = pd.to_numeric(
            df[bar_col],
            errors="coerce"
        ).dropna()

        line_values = pd.to_numeric(
            df[line_col],
            errors="coerce"
        ).dropna()

        # Means
        bar_mean = bar_values.mean() * scale_left
        line_mean = line_values.mean() * scale_right

        # Variance
        if variance == "std":
            line_var = line_values.std() * scale_right

        elif variance == "sem":
            line_var = (
                line_values.std() / np.sqrt(len(line_values))
            ) * scale_right

        else:
            line_var = 0

        bar_means.append(bar_mean)
        line_means.append(line_mean)
        line_vars.append(line_var)

    # X positions
    x = np.arange(len(csv_paths))

    # Figure
    fig, ax1 = plt.subplots(figsize=figsize)

    # -----------------------------
    # Left axis (BAR)
    # -----------------------------
    bars = ax1.bar(
        x,
        bar_means,
        width=0.4,
        alpha=0.8,
        label=bar_col,
        color="tab:blue",
    )

    ax1.set_ylabel(bar_col)
    ax1.set_xticks(x)
    ax1.set_xticklabels(x_labels, rotation=20)

    # Grid


    # -----------------------------
    # Right axis (LINE)
    # -----------------------------
    ax2 = ax1.twinx()

    y = np.array(line_means)
    v = np.array(line_vars)

    ax2.plot(
        x,
        y,
        marker="o",
        linewidth=2,
        label=line_col,
        color="tab:orange",
    )

    # Variance region
    if variance is not None:

        lower = y - v
        upper = y + v

        ax2.fill_between(
            x,
            lower,
            upper,
            alpha=0.2,
            color="tab:orange",
        )

    ax2.set_ylabel(line_col)

    # -----------------------------
    # Title
    # -----------------------------
    if title:
        plt.title(title)

    # -----------------------------
    # Combined legend
    # -----------------------------
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()

    ax1.legend(
        lines1 + lines2,
        labels1 + labels2,
        loc="best",
    )

    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(
            save_path,
            dpi=300,
            bbox_inches="tight",
        )

    plt.show()
    
def plot_acc():
    names = ['dblp-scholar', 'cora', 'imdb', 'pokemon']
    titles = ['Dblp', 'Cora', 'Imdb', 'Poke']
    titles = [r'\textit{' + t + '}' for t in titles]
    paths = []
    x_labels = []
    for i,n in enumerate(names):
        plot_size_f1(name=n,title=titles[i])
        split = [80, 0.8,0.6,0.4,0.2]
        labels = [100, 80,60,40,20]
        x_labels.append(labels)
        path = [ f'./lp/{names[i]}/{p}/results/scores/{names[i]}-{p}-s1-scores.csv' for p in split]
        paths.append(path)
        # title = r'\textit{' + title + '}'
    plot_acc_from_csv_groups(csv_groups=paths, variance='sem',line_labels=["\\textbf{Precision}", "\\textbf{Recall}", "\\textbf{F1}"], columns=['test_precision','test_recall','test_f1',],group_titles=titles,save_path=f'./lp/acc-var.pdf', x_labels_groups=x_labels)
    
def plot_size_time(name,title):
    split = [80, 0.8,0.6,0.4,0.2]
    labels = [100, 80,60,40,20]
    path = [ f'./lp/{name}/{p}/results/scores/{name}-{p}-s1-scores.csv' for p in split]
    plot_bar_line_dual_axis(csv_paths=path, variance='sem', columns=('size','popper_time_sec'),title=f'{name} rule size',save_path=f'./lp/{name}/{name}-size-time.pdf')
    
def plot_size_f1(name,title):
    split = [80, 0.8,0.6,0.4,0.2]
    labels = [100, 80,60,40,20]
    path = [ f'./lp/{name}/{p}/results/scores/{name}-{p}-s1-scores.csv' for p in split]
    plot_bar_line_dual_axis(csv_paths=path, variance='sem', columns=('size','test_f1'),title=f'{name} rule size',save_path=f'./lp/{name}/{name}-size-f1.pdf')


def plot_rulesize(name):
    split = [80, 0.8,0.6,0.4,0.2]
    labels = [100, 80,60,40,20]
    path = [ f'./lp/{name}/{p}/results/scores/{name}-{p}-s1-scores.csv' for p in split]
    plot_metrics_from_csvs(csv_paths=path, variance='sem', columns=['rules','size'],title=f'{name} rule size',save_path=f'./lp/{name}/{name}-rulesize.pdf', labels = labels)
    
def plot_runningtime(name, title):
    split = [80, 0.8,0.6,0.4,0.2]
    labels = [100, 80,60,40,20]
    path = [ f'./lp/{name}/{p}/results/scores/{name}-{p}-s1-scores.csv' for p in split]
    plot_metrics_from_csvs(csv_paths=path, variance='sem', columns=['popper_time_sec'],title=r'\textit{' + title + '}',save_path=f'./lp/{name}/{name}-time.pdf', labels = labels)
    
def count_asp_pair_patterns(file_path):
    """
    Count:
      1. Join pairs:
         att(T1,A1,V), att(T2,A2,V)

      2. Similarity pairs:
         att(T1,A1,V1), att(T2,A2,V2), sim(V1,V2)

    Only counts rules that actually contain these patterns.

    Returns:
        {
            "total_size": int,
            "join_pairs": list,
            "similarity_pairs": list
        }
    """

    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Remove ASP comments
    content = re.sub(r"%.*", "", content)

    # Split rules by '.'
    rules = [r.strip() for r in content.split(".") if r.strip()]

    total_size = 0
    all_join_pairs = []
    all_similarity_pairs = []

    att_pattern = re.compile(
        r'att\s*\(\s*([^,\s]+)\s*,\s*([^,\s]+)\s*,\s*([^)\s]+)\s*\)'
    )

    sim_pattern = re.compile(
        r'sim\s*\(\s*([^,\s]+)\s*,\s*([^)\s]+)\s*\)'
    )

    for rule in rules:

        # Extract all att atoms
        atts = []
        for m in att_pattern.finditer(rule):
            tid, attr, value = m.groups()
            atts.append({
                "tid": tid,
                "attr": attr,
                "value": value,
                "text": m.group(0)
            })

        # Extract sim atoms
        sims = []
        for m in sim_pattern.finditer(rule):
            v1, v2 = m.groups()
            sims.append((v1, v2))

        # ------------------------------------------------------------
        # Join pairs
        # ------------------------------------------------------------
        join_pairs = []

        for i in range(len(atts)):
            for j in range(i + 1, len(atts)):

                a1 = atts[i]
                a2 = atts[j]

                # same value variable => join pair
                if a1["value"] == a2["value"]:
                    pair = (a1["text"], a2["text"])
                    join_pairs.append(pair)

        # ------------------------------------------------------------
        # Similarity pairs
        # ------------------------------------------------------------
        similarity_pairs = []

        for sim_v1, sim_v2 in sims:

            matched_atts = []

            for att in atts:
                if att["value"] in {sim_v1, sim_v2}:
                    matched_atts.append(att)

            # Need two matching att atoms
            if len(matched_atts) >= 2:

                for i in range(len(matched_atts)):
                    for j in range(i + 1, len(matched_atts)):

                        a1 = matched_atts[i]
                        a2 = matched_atts[j]

                        values = {a1["value"], a2["value"]}

                        if values == {sim_v1, sim_v2}:
                            pair = (
                                a1["text"],
                                a2["text"],
                                f"sim({sim_v1},{sim_v2})"
                            )
                            similarity_pairs.append(pair)

        # Count only if rule has the pattern
        total_size += len(join_pairs)
        total_size += len(similarity_pairs)

        all_join_pairs.extend(join_pairs)
        all_similarity_pairs.extend(similarity_pairs)

    return {
        "total_size": total_size,
        "join_pairs": all_join_pairs,
        "similarity_pairs": all_similarity_pairs
    }
    
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import scienceplots


def plot_stacked_er_comparison(
    baseline_csv,
    pair1_base_csv,
    pair1_enhanced_csv,
    pair2_base_csv,
    pair2_enhanced_csv,
    labels=None,
    title=None,
    save_path=None,
):
    """
    Plot ER comparison bar chart.

    - Baseline:
        normal bar

    - Pair 1 and Pair 2:
        stacked bars showing:
            base score
            improvement from enhanced version

    Metrics used:
        - test_precision
        - test_recall
        - test_f1

    Missing / N/A values are treated as 0.

    Parameters
    ----------
    baseline_csv : str

    pair1_base_csv : str
    pair1_enhanced_csv : str

    pair2_base_csv : str
    pair2_enhanced_csv : str

    labels : list[str] or None
        Labels for:
            [baseline, pair1, pair2]

    title : str or None

    save_path : str or None
    """

    plt.style.use(["science", "ieee"])

    metrics = [
        "test_precision",
        "test_recall",
        "test_f1",
    ]

    # -----------------------------
    # Helper
    # -----------------------------
    def compute_metric_average(csv_path):

        df = pd.read_csv(csv_path)

        results = {}

        for metric in metrics:

            if metric not in df.columns:
                raise ValueError(
                    f"Column '{metric}' not found in {csv_path}"
                )

            values = pd.to_numeric(
                df[metric],
                errors="coerce"
            ).fillna(0)

            results[metric] = values.mean()

        return results

    # -----------------------------
    # Compute averages
    # -----------------------------
    baseline = compute_metric_average(baseline_csv)

    pair1_base = compute_metric_average(pair1_base_csv)
    pair1_enh = compute_metric_average(pair1_enhanced_csv)

    pair2_base = compute_metric_average(pair2_base_csv)
    pair2_enh = compute_metric_average(pair2_enhanced_csv)

    # -----------------------------
    # Labels
    # -----------------------------
    if labels is None:
        labels = [
            "Baseline",
            "Pair 1",
            "Pair 2",
        ]

    # -----------------------------
    # Plot
    # -----------------------------
    x = np.arange(len(metrics))
    width = 0.25

    fig, ax = plt.subplots(figsize=(9, 5))

    # Baseline normal bars
    baseline_values = [
        baseline[m]
        for m in metrics
    ]

    ax.bar(
        x - width,
        baseline_values,
        width,
        label=labels[0],
    )

    # -----------------------------
    # Pair 1 stacked bars
    # -----------------------------
    pair1_base_vals = [
        pair1_base[m]
        for m in metrics
    ]

    pair1_improvements = [
        max(pair1_enh[m] - pair1_base[m], 0)
        for m in metrics
    ]

    ax.bar(
        x,
        pair1_base_vals,
        width,
        label=f"{labels[1]} Base",
    )

    ax.bar(
        x,
        pair1_improvements,
        width,
        bottom=pair1_base_vals,
        label=f"{labels[1]} Improvement",
    )

    # -----------------------------
    # Pair 2 stacked bars
    # -----------------------------
    pair2_base_vals = [
        pair2_base[m]
        for m in metrics
    ]

    pair2_improvements = [
        max(pair2_enh[m] - pair2_base[m], 0)
        for m in metrics
    ]

    ax.bar(
        x + width,
        pair2_base_vals,
        width,
        label=f"{labels[2]} Base",
    )

    ax.bar(
        x + width,
        pair2_improvements,
        width,
        bottom=pair2_base_vals,
        label=f"{labels[2]} Improvement",
    )

    # -----------------------------
    # Formatting
    # -----------------------------
    ax.set_xticks(x)
    ax.set_xticklabels([
        "\\textbf{Precision}",
        "\\textbf{Recall}",
        "\\textbf{F1}",
    ])

    ax.set_ylabel("\\textbf{Avg. Score}")

    if title:
        ax.set_title(title)

    ax.legend()

    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(
            save_path,
            bbox_inches="tight",
        )

    plt.show()
    
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import scienceplots
from matplotlib.patches import Patch


import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import scienceplots
from matplotlib.patches import Patch


def plot_stacked_er_comparison_with_negative(
    baseline_csv,
    pair1_base_csv,
    pair1_enhanced_csv,
    pair2_base_csv,
    pair2_enhanced_csv,
    title=None,
    save_path=None,
):
    """
    ER comparison figure with visually separated improvements
    and degradations.

    Positive changes:
        stacked upward

    Negative changes:
        stacked downward

    Metrics:
        - test_precision
        - test_recall
        - test_f1
    """

    plt.style.use(['science', 'vibrant'])

    metrics = [
        "test_precision",
        "test_recall",
        "test_f1",
    ]

    metric_labels = [
        "\\textbf{100/40/20}",
        "\\textbf{100/40/20}",
        "\\textbf{100/40/20}",
    ]

    top_labels = ["\\textbf{P}", "\\textbf{R}", "\\textbf{F1}"]

    # -----------------------------------
    # Colors
    # -----------------------------------
    colors = {
        "baseline": [
            "#4C72B0",
            "#55A868",
            "#C44E52",
        ],

        "pair1": [
            "#8172B2",
            "#CCB974",
            "#64B5CD",
        ],

        "pair2": [
            "#937860",
            "#DA8BC3",
            "#8C8C8C",
        ],

        "improvement": "#D9EAD3",   # light green
        "degradation": "#F4CCCC",   # light red
    }

    # -----------------------------------
    # Helper
    # -----------------------------------
    def compute_averages(csv_path):

        df = pd.read_csv(csv_path)

        results = {}

        for metric in metrics:

            values = pd.to_numeric(
                df.get(metric, 0),
                errors="coerce"
            ).fillna(0)

            results[metric] = values.mean() * 100

        return results

    # -----------------------------------
    # Load data
    # -----------------------------------
    baseline = compute_averages(baseline_csv)

    pair1_base = compute_averages(pair1_base_csv)
    pair1_enh = compute_averages(pair1_enhanced_csv)

    pair2_base = compute_averages(pair2_base_csv)
    pair2_enh = compute_averages(pair2_enhanced_csv)

    # -----------------------------------
    # Plot setup
    # -----------------------------------
    x = np.arange(len(metrics))
    width = 0.25

    fig, ax = plt.subplots(figsize=(3.5, 2))

    # -----------------------------------
    # Baseline
    # -----------------------------------
    for i, metric in enumerate(metrics):

        val = baseline[metric]

        ax.bar(
            x[i] - width,
            val,
            width,
            color=colors["baseline"][i],
            edgecolor="black",
            linewidth=0.6,
        )

    # -----------------------------------
    # Pair 1
    # -----------------------------------
    for i, metric in enumerate(metrics):

        base = pair1_base[metric]
        enh = pair1_enh[metric]

        diff = enh - base

        # Base bar
        ax.bar(
            x[i],
            base,
            width,
            color=colors["pair1"][i],
            edgecolor="black",
            linewidth=0.6,
        )

        # Positive improvement
        if diff >= 0:

            ax.bar(
                x[i],
                diff,
                width,
                bottom=base,
                color=colors["improvement"],
                edgecolor="black",
                linewidth=0.6,
                hatch="//",
            )

        # Negative degradation
        else:

            ax.bar(
                x[i],
                diff,
                width,
                bottom=base,
                color=colors["degradation"],
                edgecolor="black",
                linewidth=0.6,
                hatch="\\\\",
            )

    # -----------------------------------
    # Pair 2
    # -----------------------------------
    for i, metric in enumerate(metrics):

        base = pair2_base[metric]
        enh = pair2_enh[metric]

        diff = enh - base

        ax.bar(
            x[i] + width,
            base,
            width,
            color=colors["pair2"][i],
            edgecolor="black",
            linewidth=0.6,
        )

        if diff >= 0:

            ax.bar(
                x[i] + width,
                diff,
                width,
                bottom=base,
                color=colors["improvement"],
                edgecolor="black",
                linewidth=0.6,
                hatch="//",
            )

        else:

            ax.bar(
                x[i] + width,
                diff,
                width,
                bottom=base,
                color=colors["degradation"],
                edgecolor="black",
                linewidth=0.6,
                hatch="\\\\",
            )

    # -----------------------------------
    # Formatting
    # -----------------------------------
    ax.set_xticks(x)
    ax.set_xticklabels(metric_labels)
    
    # -----------------------------------
    # Top labels: P / R / F1
    # -----------------------------------
    for i, label in enumerate(top_labels):

        ax.text(
            x[i],
            1.01,
            label,
            transform=ax.get_xaxis_transform(),
            ha="center",
            va="bottom",
            fontsize=10,
        )

    ax.set_ylim(0, 100)
    ax.set_yticks(np.arange(0, 101, 20))
    ax.set_ylabel("\\textbf{Avg. Score}")

    if title:
        ax.set_title(
        r'\textit{' + title + '}',
        pad=18,
    )

    ax.axhline(0, color="black", linewidth=0.8)

    # Legend
    legend_elements = [
        Patch(
            facecolor="#4C72B0",
            edgecolor="black",
            label="Baseline",
        ),

        Patch(
            facecolor="#8172B2",
            edgecolor="black",
            label="Pair 1 Base",
        ),

        Patch(
            facecolor="#937860",
            edgecolor="black",
            label="Pair 2 Base",
        ),

        Patch(
            facecolor="#D9EAD3",
            edgecolor="black",
            hatch="//",
            label="Improvement",
        ),

        Patch(
            facecolor="#F4CCCC",
            edgecolor="black",
            hatch="\\\\",
            label="Degradation",
        ),
    ]

    #ax.legend(handles=legend_elements)
        # Y-axis
    ax.set_ylim(0, 100)
    ax.set_yticks(np.arange(0, 101, 20))
    plt.tight_layout()

    # Save
    if save_path:
        plt.savefig(
            save_path,
            bbox_inches="tight",
        )

    plt.show()

# Multi-Dataset Version of the ER Comparison Plot




def plot_multi_dataset_er_comparison(
    dataset_configs,
    dataset_titles=None,
    title=None,
    save_path=None,
):
    """
    Plot 4 ER comparison charts in a 2x2 layout.

    Parameters
    ----------
    dataset_configs : list of dict
        Each element corresponds to one subplot.

        Each dict must contain:

        {
            "baseline_csv": ...,
            "pair1_base_csv": ...,
            "pair1_enhanced_csv": ...,
            "pair2_base_csv": ...,
            "pair2_enhanced_csv": ...,
        }

    dataset_titles : list of str
        Titles for each subplot.

    title : str
        Global figure title.

    save_path : str
        Output PDF/PNG path.
    """

    plt.style.use(['science', 'vibrant'])

    metrics = [
        "test_precision",
        "test_recall",
        "test_f1",
    ]

    metric_labels = [
        "100/40/20",
        "100/40/20",
        "100/40/20",
    ]

    top_labels = [
        "\\textbf{P}",
        "\\textbf{R}",
        "\\textbf{F1}",
    ]

    # -----------------------------------
    # Colors
    # -----------------------------------
    colors = {
        "baseline": [
            "#4C72B0",
            "#55A868",
            "#C44E52",
        ],

        "pair1": [
            "#8172B2",
            "#CCB974",
            "#64B5CD",
        ],

        "pair2": [
            "#937860",
            "#DA8BC3",
            "#8C8C8C",
        ],

        "improvement": "#D9EAD3",
        "degradation": "#F4CCCC",
    }

    # -----------------------------------
    # Helper
    # -----------------------------------
    def compute_averages(csv_path):

        df = pd.read_csv(csv_path)

        results = {}

        for metric in metrics:

            values = pd.to_numeric(
                df.get(metric, 0),
                errors="coerce"
            ).fillna(0)

            results[metric] = values.mean() * 100

        return results

    # -----------------------------------
    # Figure setup
    # -----------------------------------
    fig, axes = plt.subplots(
        1,
        4,
        figsize=(3.5, 2.5),
        sharey=True,
    )

    axes = axes.flatten()

    x = np.arange(len(metrics))
    width = 0.25

    # -----------------------------------
    # Draw each dataset
    # -----------------------------------
    for idx, config in enumerate(dataset_configs):

        ax = axes[idx]

        baseline = compute_averages(config["baseline_csv"])

        pair1_base = compute_averages(config["pair1_base_csv"])
        pair1_enh = compute_averages(config["pair1_enhanced_csv"])

        pair2_base = compute_averages(config["pair2_base_csv"])
        pair2_enh = compute_averages(config["pair2_enhanced_csv"])

        # -----------------------------------
        # Baseline
        # -----------------------------------
        for i, metric in enumerate(metrics):

            val = baseline[metric]

            ax.bar(
                x[i] - width,
                val,
                width,
                color=colors["baseline"][i],
                edgecolor="black",
                linewidth=0.6,
            )

        # -----------------------------------
        # Pair 1
        # -----------------------------------
        for i, metric in enumerate(metrics):

            base = pair1_base[metric]
            enh = pair1_enh[metric]

            diff = enh - base

            ax.bar(
                x[i],
                base,
                width,
                color=colors["pair1"][i],
                edgecolor="black",
                linewidth=0.6,
            )

            if diff >= 0:

                ax.bar(
                    x[i],
                    diff,
                    width,
                    bottom=base,
                    color=colors["improvement"],
                    edgecolor="black",
                    linewidth=0.6,
                    hatch="//",
                )

            else:

                ax.bar(
                    x[i],
                    diff,
                    width,
                    bottom=base,
                    color=colors["degradation"],
                    edgecolor="black",
                    linewidth=0.6,
                    hatch="\\\\",
                )

        # -----------------------------------
        # Pair 2
        # -----------------------------------
        for i, metric in enumerate(metrics):

            base = pair2_base[metric]
            enh = pair2_enh[metric]

            diff = enh - base

            ax.bar(
                x[i] + width,
                base,
                width,
                color=colors["pair2"][i],
                edgecolor="black",
                linewidth=0.6,
            )

            if diff >= 0:

                ax.bar(
                    x[i] + width,
                    diff,
                    width,
                    bottom=base,
                    color=colors["improvement"],
                    edgecolor="black",
                    linewidth=0.6,
                    hatch="//",
                )

            else:

                ax.bar(
                    x[i] + width,
                    diff,
                    width,
                    bottom=base,
                    color=colors["degradation"],
                    edgecolor="black",
                    linewidth=0.6,
                    hatch="\\\\",
                )

        # -----------------------------------
        # Formatting
        # -----------------------------------
        ax.set_xticks(x)
        ax.set_xticklabels(metric_labels, fontsize=5)

        ax.set_ylim(0, 100)
        ax.set_yticks(np.arange(0, 101, 20))
        ax.tick_params(axis='y', labelsize=5)
        ax.axhline(0, color="black", linewidth=0.8)

        # P / R / F1 labels
        for i, label in enumerate(top_labels):

            ax.text(
                x[i],
                1.005,
                label,
                transform=ax.get_xaxis_transform(),
                ha="center",
                va="bottom",
                fontsize=5,
            )

        # subplot title
        if dataset_titles is not None:

            ax.set_title(
                r'\textit{' + dataset_titles[idx] + '}',
                pad=10,fontsize=7
                
            )

        # y label only on left column
        if idx % 2 == 0:
            ax.set_ylabel("\\textbf{Avg. Score}", fontsize=5)

    # -----------------------------------
    # Global legend
    # -----------------------------------
    legend_elements = [
       
        Patch(
            facecolor="#D9EAD3",
            edgecolor="black",
            hatch="//",
            label="\\textbf{Improvement}",
        ),

        Patch(
            facecolor="#F4CCCC",
            edgecolor="black",
            hatch="\\\\",
            label="\\textbf{Degradation}",
        ),
    ]

    fig.legend(
        handles=legend_elements,
        loc="lower center",
        ncol=5,
        bbox_to_anchor=(0.5, 0.06),
        fontsize=5
    )

    # -----------------------------------
    # Global title
    # -----------------------------------
    if title:
        fig.suptitle(title, y=1.02)

    plt.tight_layout()
    plt.subplots_adjust(bottom=0.18)

    # -----------------------------------
    # Save
    # -----------------------------------
    if save_path:

        plt.savefig(
            save_path,
            bbox_inches="tight",
        )

    plt.show()
    
def plot_multi_dataset_er_comparison2(
    dataset_configs,
    dataset_titles=None,
    title=None,
    save_path=None,
):
    """
    Plot 4 ER comparison charts in a 1x4 layout.
    """

    plt.style.use(['science', 'vibrant'])

    metrics = [
        "test_precision",
        "test_recall",
        "test_f1",
    ]

    metric_labels = [
        "100/40/20",
        "100/40/20",
        "100/40/20",
    ]

    top_labels = [
        "\\textbf{P}",
        "\\textbf{R}",
        "\\textbf{F1}",
    ]

    colors = {
        "baseline": ["#4C72B0", "#55A868", "#C44E52"],
        "pair1": ["#8172B2", "#CCB974", "#64B5CD"],
        "pair2": ["#937860", "#DA8BC3", "#8C8C8C"],
        "improvement": "#D9EAD3",
        "degradation": "#F4CCCC",
    }

    def compute_averages(csv_path):
        df = pd.read_csv(csv_path)
        results = {}

        for metric in metrics:
            values = pd.to_numeric(
                df.get(metric, 0),
                errors="coerce"
            ).fillna(0)

            results[metric] = values.mean() * 100

        return results

    # -----------------------------
    # CHANGE: 1x4 layout
    # -----------------------------
    fig, axes = plt.subplots(
        1,
        4,
        figsize=(6.6, 1.5),
        sharey=True,
    )

    axes = axes.flatten()

    x = np.arange(len(metrics))
    width = 0.25

    for idx, config in enumerate(dataset_configs):

        ax = axes[idx]

        baseline = compute_averages(config["baseline_csv"])
        pair1_base = compute_averages(config["pair1_base_csv"])
        pair1_enh = compute_averages(config["pair1_enhanced_csv"])
        pair2_base = compute_averages(config["pair2_base_csv"])
        pair2_enh = compute_averages(config["pair2_enhanced_csv"])

        # Baseline
        for i, metric in enumerate(metrics):
            ax.bar(
                x[i] - width,
                baseline[metric],
                width,
                color=colors["baseline"][i],
                edgecolor="black",
                linewidth=0.6,
            )

        # Pair 1
        for i, metric in enumerate(metrics):
            base = pair1_base[metric]
            enh = pair1_enh[metric]
            diff = enh - base

            ax.bar(
                x[i],
                base,
                width,
                color=colors["pair1"][i],
                edgecolor="black",
                linewidth=0.6,
            )

            ax.bar(
                x[i],
                diff,
                width,
                bottom=base,
                color=colors["improvement"] if diff >= 0 else colors["degradation"],
                edgecolor="black",
                linewidth=0.6,
                hatch="//" if diff >= 0 else "\\\\",
            )

        # Pair 2
        for i, metric in enumerate(metrics):
            base = pair2_base[metric]
            enh = pair2_enh[metric]
            diff = enh - base

            ax.bar(
                x[i] + width,
                base,
                width,
                color=colors["pair2"][i],
                edgecolor="black",
                linewidth=0.6,
            )

            ax.bar(
                x[i] + width,
                diff,
                width,
                bottom=base,
                color=colors["improvement"] if diff >= 0 else colors["degradation"],
                edgecolor="black",
                linewidth=0.6,
                hatch="//" if diff >= 0 else "\\\\",
            )

        # Formatting
        ax.set_xticks(x)
        ax.set_xticklabels(metric_labels, fontsize=5)

        ax.set_ylim(0, 100)
        ax.set_yticks(np.arange(0, 101, 20))
        ax.tick_params(axis='y', labelsize=5)

        ax.axhline(0, color="black", linewidth=0.8)

        # P/R/F1 labels
        for i, label in enumerate(top_labels):
            ax.text(
                x[i],
                1.005,
                label,
                transform=ax.get_xaxis_transform(),
                ha="center",
                va="bottom",
                fontsize=5,
            )

        if dataset_titles is not None:
            ax.set_title(
                r'\textit{' + dataset_titles[idx] + '}',
                pad=10,
                fontsize=7,
            )

        # CHANGE: only first subplot gets ylabel
        if idx == 0:
            ax.set_ylabel("\\textbf{Avg. Score}", fontsize=5)

    legend_elements = [
        Patch(
            facecolor="#D9EAD3",
            edgecolor="black",
            hatch="//",
            label="\\textbf{Improvement}",
        ),
        Patch(
            facecolor="#F4CCCC",
            edgecolor="black",
            hatch="\\\\",
            label="\\textbf{Degradation}",
        ),
    ]

    fig.legend(
        handles=legend_elements,
        loc="lower center",
        ncol=5,
        bbox_to_anchor=(0.5, -0.05),
        fontsize=5,
    )

    if title:
        fig.suptitle(title, y=1.05)

    plt.tight_layout()
    plt.subplots_adjust(bottom=0.22, top=0.82)

    if save_path:
        plt.savefig(save_path, bbox_inches="tight")

    plt.show()



def dc_result_cora():
    plot_stacked_er_comparison_with_negative(baseline_csv='./lp/cora/80/results/scores/cora-80-s1-scores.csv',pair1_base_csv='./lp/cora/0.4/results/scores/cora-0.4-s1-scores.csv', pair1_enhanced_csv='./lp/cora/0.4/results/scores/cora-0.4-s1-dc-scores3.csv'
                               ,pair2_base_csv='./lp/cora/0.2/results/scores/cora-0.2-s1-scores.csv', pair2_enhanced_csv='./lp/cora/0.2/results/scores/cora-0.2-s1-dc-scores3.csv',save_path='./lp/cora/dc-result.pdf', title='Cora' )
def dc_result_dblp():
        plot_stacked_er_comparison_with_negative(baseline_csv='./lp/dblp-scholar/80/results/scores/dblp-scholar-80-s1-scores.csv',pair1_base_csv='./lp/dblp-scholar/0.4/results/scores/dblp-scholar-0.4-s1-scores.csv', pair1_enhanced_csv='./lp/dblp-scholar/0.4/results/scores/dblp-scholar-0.4-s1-dc-scores3.csv'
                               ,pair2_base_csv='./lp/dblp-scholar/0.2/results/scores/dblp-scholar-0.2-s1-scores.csv', pair2_enhanced_csv='./lp/dblp-scholar/0.2/results/scores/dblp-scholar-0.2-s1-dc-scores3.csv',save_path='./lp/dblp-scholar/dc-result.pdf')



def plot_dc_acc():
    names = ['dblp-scholar', 'cora', 'imdb', 'pokemon']
    titles = ['Dblp', 'Cora', 'Imdb', 'Poke']
    titles = [r'\textit{' + t + '}' for t in titles]
    paths = []
    x_labels = []
    for i,n in enumerate(names):
        plot_size_f1(name=n,title=titles[i])
        split = [80, 0.8,0.6,0.4,0.2]
        labels = [100, 80,60,40,20]
        x_labels.append(labels)
        path = [ f'./lp/{names[i]}/{p}/results/scores/{names[i]}-{p}-s1-scores.csv' for p in split]
        paths.append(path)
        # title = r'\textit{' + title + '}'
    plot_acc_from_csv_groups(csv_groups=paths, variance='sem',line_labels=["\\textbf{Precision}", "\\textbf{Recall}", "\\textbf{F1}"], columns=['test_precision','test_recall','test_f1',],group_titles=titles,save_path=f'./lp/acc-var.pdf', x_labels_groups=x_labels)
if __name__ == "__main__":
    
    
    path = './lp/pokemon/80/results/scores/pokemon-80-s1-scores.csv'
    path2 = './lp/pokemon/80/resultspw/scores/pokemon-80-s1-scores.csv'
    # path = './lp/cora/80/results/scores/cora-80-s1-scores.csv'
    # path = './lp/imdb/80/results/scores/imdb-80-s1-scores.csv'
    # path = './lp/imdb/80/resultspw/scores/imdb-80-s1-scores.csv'
    # print(compute_stats(path2))
    print(count_asp_pair_patterns('./lp/dblp-scholar/80/results/rules/dblp-scholar-80-s2-t0.5-d0.025.lp'))
    # names = ['dblp-scholar', 'cora', 'imdb']
    # titles = ['Dblp', 'Cora', 'Imdb']
    # for i,n in enumerate(names):
    #     plot_size_f1(name=n,title=titles[i])
    # plot_stacked_er_comparison_with_negative(baseline_csv='./lp/imdb/80/results/scores/imdb-80-s1-scores.csv',pair1_base_csv='./lp/imdb/0.4/results/scores/imdb-0.4-s1-scores.csv', pair1_enhanced_csv='./lp/imdb/0.4/results/scores/imdb-0.4-s1-dc-scores2.csv'
    #                            ,pair2_base_csv='./lp/imdb/0.2/results/scores/imdb-0.2-s1-scores.csv', pair2_enhanced_csv='./lp/imdb/0.2/results/scores/imdb-0.2-s1-dc-scores2.csv',save_path='./lp/imdb/dc-result.pdf')
    # plot_acc()
    names = ['dblp-scholar', 'cora', 'imdb', 'pokemon']
    base_paths = [f'./lp/{n}/80/results/scores/{n}-80-s1-scores.csv' for n in names]
    p1_paths = [f'./lp/{n}/0.4/results/scores/{n}-0.4-s1-dc-scores3.csv' for n in names]
    p1_base_paths = [f'./lp/{n}/0.4/results/scores/{n}-0.4-s1-scores.csv' for n in names]
    p2_paths = [f'./lp/{n}/0.2/results/scores/{n}-0.2-s1-dc-scores3.csv' for n in names]
    p2_base_paths = [f'./lp/{n}/0.2/results/scores/{n}-0.2-s1-scores.csv' for n in names]
    dataset_titles = ['Dblp', 'Cora', 'Imdb', 'Poke']
    plot_multi_dataset_er_comparison2(
    dataset_configs=[{
            "baseline_csv": bp,
            "pair1_base_csv": bp1,
            "pair1_enhanced_csv": p1,
            "pair2_base_csv": bp2,
            "pair2_enhanced_csv":p2,
        } for n,bp,p1,bp1,p2,bp2 in zip(names,base_paths,p1_paths,p1_base_paths,p2_paths, p2_base_paths)
        
     
    ],
    dataset_titles=dataset_titles,
    # title="ER Comparison Across Datasets",
    save_path="./lp/dc-result2.pdf",
)

    # plot_runningtime('dblp-scholar', title='Dblp')

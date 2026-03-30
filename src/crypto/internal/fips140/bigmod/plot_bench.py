#!/usr/bin/env python3
"""
Parse benchstat raw output files (bench_legacy.txt, bench_fixed.txt) and
bench_comparison.txt, then produce a grouped bar chart comparing legacy vs
fixed extendedGCD performance per limb size.

Usage:
    python3 plot_bench.py testdata/bench_comparison.txt
    python3 plot_bench.py testdata/bench_comparison.txt output.pdf

Expects bench_legacy.txt and bench_fixed.txt in the same directory as
bench_comparison.txt (for computing standard deviations from raw data).
"""

import os
import re
import sys
from collections import defaultdict

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np


def parse_raw_file(path):
    """Parse a raw benchmark output file and return {limbs: [ns/op values across all pairs and counts]}."""
    data = defaultdict(list)
    pattern = re.compile(
        r'BenchmarkExtendedGCD_Limbs_(\d+)/pair_\d+-\d+\s+\d+\s+([\d.]+)\s+ns/op'
    )
    with open(path) as f:
        for line in f:
            m = pattern.search(line)
            if m:
                limbs = int(m.group(1))
                ns = float(m.group(2))
                data[limbs].append(ns)
    return data


def parse_comparison(path):
    """Parse bench_comparison.txt for speedup percentages."""
    speedups = defaultdict(list)
    pattern = re.compile(
        r'ExtendedGCD_Limbs_(\d+)/pair_\d+-\d+\s+.*\s+(-?[\d.]+)%\s+\(p='
    )
    with open(path) as f:
        for line in f:
            m = pattern.search(line)
            if m:
                limbs = int(m.group(1))
                speedups[limbs].append(float(m.group(2)))
    return {l: np.mean(v) for l, v in speedups.items()}


def format_time(us):
    """Format microseconds as µs."""
    if us < 1:
        return f"{us:.2f} µs"
    elif us < 10:
        return f"{us:.1f} µs"
    elif us < 1000:
        return f"{us:.0f} µs"
    else:
        return f"{us:,.0f} µs"


def plot(legacy_data, fixed_data, speedups, output_path):
    limb_sizes = sorted(set(legacy_data.keys()) & set(fixed_data.keys()))
    x = np.arange(len(limb_sizes))
    width = 0.35

    # Convert from ns to µs.
    legacy_means = [np.mean(legacy_data[l]) / 1e3 for l in limb_sizes]
    legacy_stds = [np.std(legacy_data[l]) / 1e3 for l in limb_sizes]
    fixed_means = [np.mean(fixed_data[l]) / 1e3 for l in limb_sizes]
    fixed_stds = [np.std(fixed_data[l]) / 1e3 for l in limb_sizes]

    # Single-column width in a double-column document (~3.5in).
    fig, ax = plt.subplots(figsize=(3.5, 3.2))
    plt.rcParams.update({'font.size': 7})

    legacy_color = '#D62728'
    verified_color = '#2CA02C'

    bars_legacy = ax.bar(
        x - width / 2, legacy_means, width,
        yerr=legacy_stds, capsize=2,
        label='Unverified standard library', color=legacy_color, alpha=1, edgecolor='black', linewidth=0.3,
    )
    bars_fixed = ax.bar(
        x + width / 2, fixed_means, width,
        yerr=fixed_stds, capsize=2,
        label='Our verified implementation', color=verified_color, alpha=1, edgecolor='black', linewidth=0.3,
    )

    # Add average duration labels inside bars.
    for i, (bar, val) in enumerate(zip(bars_legacy, legacy_means)):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            val * 0.85,
            format_time(val), ha='center', va='top', fontsize=4,
            rotation=90, color='white', fontweight='bold',
        )
    for i, (bar, val) in enumerate(zip(bars_fixed, fixed_means)):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            val * 0.85,
            format_time(val), ha='center', va='top', fontsize=4,
            rotation=90, color='white', fontweight='bold',
        )

    # Set up axes before computing arrow angles (log scale affects transforms).
    ax.set_xlabel('Bit size', fontsize=7)
    ax.set_ylabel('Time per invocation (µs)', fontsize=7)
    ax.set_title('extendedGCD: Original vs Verified', fontsize=8)
    ax.set_xticks(x)
    ax.set_xticklabels([str(l * 64) for l in limb_sizes], rotation=45, ha='right')
    ax.tick_params(axis='both', labelsize=5.5)
    ax.set_yscale('log')
    min_val = min(min(fixed_means), min(legacy_means))
    max_val = max(max(legacy_means), max(fixed_means))
    ax.set_ylim(bottom=min_val * 0.15, top=max_val * 4)
    ax.legend(fontsize=6)
    ax.grid(axis='y', alpha=0.3)
    plt.tight_layout()

    # Collect arrow endpoints.
    arrow_data = []
    for i, l in enumerate(limb_sizes):
        sp = speedups.get(l, 0)
        legacy_top = legacy_means[i] + legacy_stds[i]
        fixed_top = fixed_means[i] + fixed_stds[i]

        # Arrow spans twice the bar pair width for visibility.
        x_mid = x[i]
        half_span = width  # double the default width/2
        x_legacy = x_mid - half_span
        x_fixed = x_mid + half_span
        # Interpolate y on log scale between legacy and fixed tops.
        log_legacy = np.log10(legacy_top)
        log_fixed = np.log10(fixed_top)
        y_legacy = 10 ** (log_legacy + (log_legacy - log_fixed) * 0.5) * 1.6
        y_fixed = 10 ** (log_fixed - (log_legacy - log_fixed) * 0.5) * 1.6

        ax.annotate(
            '', xy=(x_fixed, y_fixed), xytext=(x_legacy, y_legacy),
            arrowprops=dict(
                arrowstyle='->', color=verified_color, lw=1.5,
                connectionstyle='arc3,rad=0',
            ),
        )
        arrow_data.append((x_legacy, y_legacy, x_fixed, y_fixed, sp))

    # Draw to finalize transforms (log scale, tight_layout already applied).
    fig.canvas.draw()

    # Add labels rotated to match each arrow's visual angle.
    for x_legacy, y_legacy, x_fixed, y_fixed, sp in arrow_data:
        p_legacy = ax.transData.transform((x_legacy, y_legacy))
        p_fixed = ax.transData.transform((x_fixed, y_fixed))
        angle_deg = np.degrees(np.arctan2(
            p_fixed[1] - p_legacy[1],
            p_fixed[0] - p_legacy[0],
        ))

        x_mid = (x_legacy + x_fixed) / 2
        y_mid = np.sqrt(y_legacy * y_fixed)
        ax.text(
            x_mid, y_mid * 1.25,
            f"−{abs(sp):.0f}%",
            ha='center', va='bottom', fontsize=5.5, fontweight='bold',
            color=verified_color, rotation=angle_deg, rotation_mode='anchor',
        )

    plt.savefig(output_path, bbox_inches='tight')
    print(f"Saved plot to {output_path}")


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <bench_comparison.txt> [output.pdf]", file=sys.stderr)
        sys.exit(1)

    comparison_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) > 2 else comparison_path.replace('.txt', '.pdf')

    data_dir = os.path.dirname(comparison_path)
    legacy_path = os.path.join(data_dir, 'bench_legacy.txt')
    fixed_path = os.path.join(data_dir, 'bench_fixed.txt')

    legacy_data = parse_raw_file(legacy_path)
    fixed_data = parse_raw_file(fixed_path)
    speedups = parse_comparison(comparison_path)

    if not legacy_data or not fixed_data:
        print("No benchmark data found in raw files.", file=sys.stderr)
        sys.exit(1)

    plot(legacy_data, fixed_data, speedups, output_path)


if __name__ == '__main__':
    main()

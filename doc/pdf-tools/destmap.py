# Maps each source .rst "stem" (path relative to source/, no extension)
# to its destination location under content/docs/, plus ordering weight.
#
# value = (section_folder, dest_slug, is_section_index, weight_within_section)
# section_folder == "" means directly under content/docs/

DEST_MAP = {
    "home": ("", "_index", True, 0),

    "1_techniques/1_techniques": ("techniques", "_index", True, 0),
    "1_techniques/2_kinduction": ("techniques", "kinduction", False, 2),
    "1_techniques/3_invgen": ("techniques", "invgen", False, 3),
    "1_techniques/4_ic3": ("techniques", "ic3", False, 4),

    "2_input/1_lustre": ("inputs-and-outputs", "lustre", False, 1),
    "2_input/2_arrays": ("inputs-and-outputs", "arrays", False, 2),
    "2_input/3_machine_ints": ("inputs-and-outputs", "machine-ints", False, 3),
    "2_input/4_refinement_types": ("inputs-and-outputs", "refinement-types", False, 4),
    "2_input/5_enums": ("inputs-and-outputs", "enums", False, 5),
    "2_input/6_history_type": ("inputs-and-outputs", "history-type", False, 6),
    "2_input/7_abstract_types": ("inputs-and-outputs", "abstract-types", False, 7),
    "2_input/8_polymorphic_types": ("inputs-and-outputs", "polymorphic-types", False, 8),
    "2_input/9_tuples": ("inputs-and-outputs", "tuples", False, 9),
    "2_input/10_sets": ("inputs-and-outputs", "sets", False, 10),
    "2_input/11_maps": ("inputs-and-outputs", "maps", False, 11),
    "2_input/12_subranges": ("inputs-and-outputs", "subranges", False, 12),
    "2_input/13_records": ("inputs-and-outputs", "records", False, 13),
    "2_input/14_algebraic_datatypes": ("inputs-and-outputs", "algebraic-datatypes", False, 14),
    "3_output/2_machine_readable": ("inputs-and-outputs", "machine-readable-output", False, 15),
    "3_output/3_exit_codes": ("inputs-and-outputs", "exit-codes", False, 16),

    "9_other/2_contract_semantics": ("advanced-features", "contract-semantics", False, 1),
    "9_other/1_post_analyses": ("advanced-features", "post-analyses", False, 2),
    "9_other/3_test_generation": ("advanced-features", "test-generation", False, 3),
    "9_other/5_proofs": ("advanced-features", "proofs", False, 4),
    "9_other/6_contract_generation": ("advanced-features", "contract-generation", False, 5),
    "9_other/9_invariant_printing": ("advanced-features", "invariant-printing", False, 6),
    "9_other/8_interpreter": ("advanced-features", "interpreter", False, 7),
    "9_other/14_contract_monitor": ("advanced-features", "contract-monitor", False, 8),
    "9_other/10_inductive_validity_core": ("advanced-features", "inductive-validity-core", False, 9),
    "9_other/11_minimal_cut_set": ("advanced-features", "minimal-cut-set", False, 10),
    "9_other/12_contract_check": ("advanced-features", "contract-check", False, 11),
    "9_other/13_assumption_generation": ("advanced-features", "assumption-generation", False, 12),

    "9_other/license": ("", "license", False, 5),
}

SECTIONS = [
    # (folder, title, weight)
    ("techniques", "Techniques", 2),
    ("inputs-and-outputs", "Inputs and Outputs", 3),
    ("advanced-features", "Advanced Features", 4),
]

def dest_url_path(stem):
    """Return the content-relative path (no extension) used for {{< relref >}} targets."""
    section, slug, is_index, _ = DEST_MAP[stem]
    parts = ["/docs"]
    if section:
        parts.append(section)
    if not is_index:
        parts.append(slug)
    return "/".join(parts)

def dest_file_path(stem, root="content/docs"):
    """Return the filesystem path (with .md) for this source stem's destination."""
    section, slug, is_index, _ = DEST_MAP[stem]
    fname = "_index.md" if is_index else f"{slug}.md"
    if section:
        return f"{root}/{section}/{fname}"
    return f"{root}/{fname}"

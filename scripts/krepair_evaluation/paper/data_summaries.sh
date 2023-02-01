scriptsdir=$(dirname $0)

bash ${scriptsdir}/data_summary.sh '/data*/test_experiment/j8_krepair_out*' | tee krepair_experiment_j8.csv 

bash ${scriptsdir}/data_summary.sh '/data*/test_experiment/j1_krepair_out*' | tee krepair_experiment_j1.csv 

bash ${scriptsdir}/runtime_summary.sh '/data*/test_experiment/krepair_only_cached*' | tee krepair_runtime_cached.csv 

bash ${scriptsdir}/runtime_summary.sh '/data*/test_experiment/krepair_only_uncached*' | tee krepair_runtime_uncached.csv 

bash ${scriptsdir}/randconfig_summary.sh '/data2/test_experiment/randconfig' | tee randconfig_coverage.csv

bash ${scriptsdir}/change_summary.sh '/data*/test_experiment/j8_krepair_out*' | tee change_summary.csv 

bash ${scriptsdir}/change_summary_allnoconfig.sh '/data*/test_experiment/j8_krepair_out*' '/data2/test_experiment/inputs/linux' | tee change_summary_allnoconfig.csv 

bash ${scriptsdir}/config_counts.sh | tee config_counts.csv 

klocalizer -a x86_64 arch/x86/kernel/irq_64.o # should pass
klocalizer -a i386 arch/x86/kernel/irq_32.o # should pass
klocalizer -a x86_64 arch/x86/kernel/irq_32.o # should fail
klocalizer -a i386 arch/x86/kernel/irq_64.o # should fail

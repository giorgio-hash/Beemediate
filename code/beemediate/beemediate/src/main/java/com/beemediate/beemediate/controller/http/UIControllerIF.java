package com.beemediate.beemediate.controller.http;

import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;

/**
 * Controller Spring MVC che gestisce l'entry point (la home page) dell'applicazione web.
 */
@RequestMapping(path = "/")
@SuppressWarnings("PMD.ImplicitFunctionalInterface")
public interface UIControllerIF{

	/**
	 * Restituisce un'interfaccia grafica per interagire con l'applicativo
	 * @return
	 */
	@GetMapping("/")
	String getUI(Model model);
	
}

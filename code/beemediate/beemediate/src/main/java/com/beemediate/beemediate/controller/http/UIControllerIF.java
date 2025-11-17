package com.beemediate.beemediate.controller.http;

import org.springframework.ui.Model;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;

@RequestMapping(path = "/")
public interface UIControllerIF{

	/**
	 * Restituisce un'interfaccia grafica per interagire con l'applicativo
	 * @return
	 */
	@GetMapping("/")
	public String getUI(Model model);
	
}

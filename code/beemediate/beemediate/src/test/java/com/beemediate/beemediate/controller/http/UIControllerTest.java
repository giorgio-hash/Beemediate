package com.beemediate.beemediate.controller.http;

import org.junit.Before;
import org.junit.Test;
import org.springframework.test.web.servlet.MockMvc;
import org.springframework.test.web.servlet.setup.MockMvcBuilders;

import com.beemediate.beemediate.controller.http.impl.UIController;


import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.get;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.status;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.view;


/**
 * UIControllerTest is a test class for the UIController.
 * It uses MockMvc to perform HTTP requests and verify the responses.
 */
public class UIControllerTest {

    /**
     * MockMvc instance used to perform requests to the UIController.
     */
    private MockMvc mockMvc;

    /**
     * Sets up the test environment before each test method.
     * Initializes the UIController and the MockMvc instance.
     */
    @Before
    public void setUp() {
        UIController uiController = new UIController();
        this.mockMvc = MockMvcBuilders.standaloneSetup(uiController).build();
    }

    /**
     * Tests that the GET request to the root URL returns the correct view name.
     * 
     * @throws Exception if an error occurs during the request or response verification.
     */
    @Test
    public void testGetUI_ReturnsCorrectViewName() throws Exception {
        String urlTemplate = "/"; 

        this.mockMvc.perform(get(urlTemplate))
                .andExpect(status().isOk())
                .andExpect(view().name("beemediate-ui.html"));
    }
}